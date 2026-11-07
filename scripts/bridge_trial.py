#!/usr/bin/env python3
"""Try ranked bridge candidates in Lean (#415). CANDIDATES ONLY.

Input is the JSON of `truth bridges --json` and the constants export of
`scripts/StatementConstants.lean` (for the declarations' modules). The tool
writes one throwaway Lean file that imports those modules, Aesop and the
`#bridge_try` command of `scripts/BridgeTrial.lean`, runs it once with
`lake env lean`, and prints a JSON report. It never writes corpus records.

A closed goal shows only that these Lean declarations compose under the
reported instantiation. It does not certify the fidelity of any reading
(AGENTS.md invariants 6 and 16) and it is not a verified result: a worker
must still record an inference, argument, frozen Challenge, Solution and
result and pass the usual binding, Comparator and NanoDa gates. A goal that
stays open is NOT a refutation.

Run after `lake build` and under the heavy-job lock, for example:

    flock /tmp/moenarch/truth-core-heavy.lock \\
      python3 scripts/bridge_trial.py --bridges bridges.json \\
        --constants constants.json --per-target 3 > trials.json
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
COMMAND = ROOT / "scripts" / "BridgeTrial.lean"
NAME = re.compile(r"^[A-Za-z_][A-Za-z0-9_'.]*$")
LINE = re.compile(r"BRIDGE-JSON (\{.*\})\s*$")
ARITIES = ("singles", "pairs", "triples")


def select(report: dict[str, Any], per_target: int) -> list[dict[str, Any]]:
    """Up to `per_target` candidates per target, interleaving arities by rank."""
    chosen = []
    for target in report.get("targets", []):
        if "skipped" in target:
            continue
        ranked = [target.get(arity, []) for arity in ARITIES]
        picked: list[dict[str, Any]] = []
        for rank in range(max(map(len, ranked), default=0)):
            for candidates in ranked:
                if rank < len(candidates) and len(picked) < per_target:
                    picked.append(candidates[rank])
        for candidate in picked:
            chosen.append({
                "target_statement_id": target["statement_id"],
                "target_declaration": target["lean_declaration"],
                "statement_ids": candidate["statement_ids"],
                "lean_declarations": candidate["lean_declarations"],
                "score": candidate["score"],
            })
    return chosen


def lean_source(trials: list[dict[str, Any]], modules: dict[str, str], heartbeats: int) -> str:
    """The throwaway Lean file: imports, the trial command, one line per trial."""
    names = set()
    for trial in trials:
        names.add(trial["target_declaration"])
        names.update(trial["lean_declarations"])
    bad = sorted(name for name in names if not NAME.fullmatch(name))
    if bad:
        raise ValueError(f"declaration names must be plain identifiers: {bad}")
    missing = sorted(name for name in names if not modules.get(name))
    if missing:
        raise ValueError(f"no module recorded for: {missing}")
    imports = sorted({modules[name] for name in names} | {"Aesop"})
    lines = [f"import {module}" for module in imports]
    lines.append(COMMAND.read_text())
    lines.append(f"set_option maxHeartbeats {heartbeats}")
    for index, trial in enumerate(trials):
        premises = " ".join(trial["lean_declarations"])
        lines.append(f'#bridge_try "{index}" {trial["target_declaration"]} from {premises}')
    return "\n".join(lines) + "\n"


def classify(outcome: dict[str, Any]) -> str:
    if "error" in outcome:
        return "error"
    if not outcome.get("closed_by"):
        return "open"
    if outcome.get("premises_refuted_by"):
        return "closed_vacuous"
    if outcome.get("target_alone_closed_by"):
        return "closed_without_premises"
    if outcome.get("generalized"):
        return "closed_generalized"
    return "closed"


def parse(output: str, trials: list[dict[str, Any]]) -> list[dict[str, Any]]:
    outcomes: dict[int, dict[str, Any]] = {}
    for line in output.splitlines():
        match = LINE.search(line)
        if match:
            outcome = json.loads(match.group(1))
            outcomes[int(outcome.pop("label"))] = outcome
    rows = []
    for index, trial in enumerate(trials):
        outcome = outcomes.get(index, {"error": "no trial output (Lean file failed or timed out)"})
        rows.append({**trial, **outcome, "status": classify(outcome)})
    return rows


def run(trials: list[dict[str, Any]], modules: dict[str, str], heartbeats: int,
        timeout: int, keep: Path | None) -> tuple[list[dict[str, Any]], str]:
    source = lean_source(trials, modules, heartbeats)
    with tempfile.TemporaryDirectory() as directory:
        path = keep or Path(directory) / "BridgeTrialRun.lean"
        path.write_text(source)
        try:
            completed = subprocess.run(
                ["python3", "scripts/worker_env.py", "--", "lake", "env", "lean", str(path)],
                cwd=ROOT, capture_output=True, text=True, timeout=timeout)
            output = completed.stdout + completed.stderr
        except subprocess.TimeoutExpired as error:
            output = (error.stdout or b"").decode() if isinstance(error.stdout, bytes) else (error.stdout or "")
            output += f"\ntimed out after {timeout}s"
    errors = [line for line in output.splitlines() if ": error" in line][:20]
    return parse(output, trials), "\n".join(errors)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--bridges", required=True, type=Path, help="truth bridges --json output")
    parser.add_argument("--constants", required=True, type=Path, help="StatementConstants.lean output")
    parser.add_argument("--per-target", type=int, default=3)
    parser.add_argument("--heartbeats", type=int, default=20000, help="maxHeartbeats per tactic attempt")
    parser.add_argument("--timeout", type=int, default=900, help="wall-clock seconds for the whole Lean run")
    parser.add_argument("--keep", type=Path, help="also write the generated Lean file here")
    args = parser.parse_args(argv)
    report = json.loads(args.bridges.read_text())
    modules = {row["declaration"]: row.get("module", "")
               for row in json.loads(args.constants.read_text())}
    trials = select(report, args.per_target)
    rows, errors = run(trials, modules, args.heartbeats, args.timeout, args.keep)
    counts: dict[str, int] = {}
    for row in rows:
        counts[row["status"]] = counts.get(row["status"], 0) + 1
    json.dump({
        "mode": "Lean trial of advisory candidates; NOT a verified result, fidelity judgment or refutation",
        "tactics": ["assumption", "solve_by_elim", "simp_all", "aesop", "grind"],
        "heartbeats": args.heartbeats,
        "status_counts": counts,
        "status_meaning": {
            "closed": "the goal closed with every premise binder matched by name and type and both controls open",
            "closed_generalized": "closed only with some premise binders universally quantified (a stronger reading)",
            "closed_without_premises": "the target closed alone: the candidate is not needed",
            "closed_vacuous": "the premises prove False under this instantiation",
            "open": "no tactic closed the goal; this is NOT a refutation",
            "error": "the trial could not be built (see goal/error)",
        },
        "lean_errors": errors,
        "trials": rows,
    }, sys.stdout, indent=1, ensure_ascii=False)
    print()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
