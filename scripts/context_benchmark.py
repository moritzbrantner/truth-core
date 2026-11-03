#!/usr/bin/env python3
"""Replay historical research PRs to compare argument context packs with the dossier workflow.

For each merged PR in `testdata/context-benchmark.json`, the repository is checked
out at the PR's base (first parent of its merge commit). The *needed context* is
derived from the PR itself: every statement, argument, result, attempt, model,
configuration or candidate ID that already existed at the base and that the PR's
corpus records newly cite (references a modified record already had are not
counted), plus every existing result whose module the PR's Lean files newly
import (generated `TruthCore/Imports/` aggregators excluded). Definitions, disambiguations, claims and sources are
excluded: they are looked up by ID rather than discovered.

The anchor is the existing result directly imported by the PR's new Lean files
(alphabetically first when several), i.e. the "Reuse" line of its brief.
Two workflows are then run at the base and compared on bytes read, tool calls,
wall time and recall of the needed IDs:

* baseline: `corpus.py related <conclusion>` and `corpus.py dossier` for the
  anchor's conclusion and each premise (the documented proposition-reuse route);
* context: one `corpus.py context <anchor>` call, run with this checkout's scripts.

Recall is a lexical proxy: an ID counts as surfaced when it appears in the output.
It measures navigation coverage, not understanding or proof progress.
"""
from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
import tempfile
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TASKS = ROOT / "scripts" / "testdata" / "context-benchmark.json"
TOKEN = re.compile(r"[A-Z][A-Z0-9]*(?:-[A-Z0-9]+)+")
COUNTED = ("statements", "arguments", "results", "attempts", "models", "configurations", "candidates")


def git(*args: str, cwd: Path = ROOT) -> str:
    return subprocess.check_output(["git", *args], cwd=cwd, text=True)


def base_ids(tree: Path) -> dict[str, str]:
    ids = {}
    for kind in COUNTED:
        for path in (tree / "corpus" / kind).glob("*.json"):
            record = json.loads(path.read_text(encoding="utf-8"))
            if isinstance(record.get("id"), str):
                ids[record["id"]] = kind
    return ids


def strings(value):
    if isinstance(value, str):
        yield value
    elif isinstance(value, list):
        for item in value:
            yield from strings(item)
    elif isinstance(value, dict):
        for item in value.values():
            yield from strings(item)


def needed_context(merge: str, tree: Path) -> tuple[set[str], str]:
    """Existing IDs the PR cited, and its anchor (directly imported existing result)."""
    known = base_ids(tree)
    results = {}
    for path in (tree / "corpus" / "results").glob("*.json"):
        record = json.loads(path.read_text(encoding="utf-8"))
        for key in ("solution_module", "challenge_module"):
            if record.get(key):
                results[record[key]] = record["id"]
    changed = [line.split("\t") for line in git("diff", "--name-status", "--no-renames", f"{merge}^1", merge).splitlines()]
    needed: set[str] = set()
    imported: set[str] = set()
    for status, path in changed:
        if status == "D":
            continue
        text = git("show", f"{merge}:{path}")
        before = git("show", f"{merge}^1:{path}") if status == "M" else ""
        if path.startswith("corpus/") and path.endswith(".json"):
            # Only references the PR introduced: a modified record's old references were not its task context.
            record = json.loads(text)
            own = record.get("id") if isinstance(record, dict) else None
            old = set(strings(json.loads(before))) if before else set()
            needed.update(s for s in strings(record) if s in known and s != own and s not in old)
        elif path.startswith("TruthCore/") and path.endswith(".lean") and not path.startswith("TruthCore/Imports/"):
            # Generated aggregators import everything; they are not reuse.
            added = set(re.findall(r"^import\s+(\S+)", text, re.M)) - set(re.findall(r"^import\s+(\S+)", before, re.M))
            imported.update(results[module] for module in added if module in results)
    needed |= imported
    if not imported:
        raise SystemExit(f"{merge}: no existing result is imported; choose another task")
    return needed, sorted(imported)[0]


def run(command: list[str], cwd: Path) -> tuple[str, float]:
    start = time.monotonic()
    completed = subprocess.run(command, cwd=cwd, text=True, capture_output=True)
    if completed.returncode:
        raise SystemExit(f"{' '.join(command)} failed in {cwd}: {completed.stderr.strip()}")
    return completed.stdout, time.monotonic() - start


def measure(outputs: list[tuple[str, float]], needed: set[str]) -> dict:
    text = "\n".join(output for output, _ in outputs)
    surfaced = needed.intersection(TOKEN.findall(text))
    return {"calls": len(outputs), "bytes": len(text.encode()), "seconds": round(sum(t for _, t in outputs), 1),
            "recall": round(len(surfaced) / len(needed), 3) if needed else None,
            "missed": sorted(needed - surfaced)}


def replay(task: dict, scratch: Path) -> dict:
    merge = git("rev-parse", task["merge"]).strip()
    tree = scratch / merge[:12]
    git("worktree", "add", "--quiet", "--detach", "--force", str(tree), f"{merge}^1")
    try:
        needed, anchor = needed_context(merge, tree)
        # The context command does not exist at historical bases: run this checkout's
        # scripts against the base corpus/Lean tree (their ROOT is the parent directory).
        head_scripts = tree / "scripts-head"
        shutil.copytree(ROOT / "scripts", head_scripts, ignore=shutil.ignore_patterns("__pycache__", "testdata"))
        record = json.loads((tree / "corpus" / "arguments" / f"{anchor}.json").read_text(encoding="utf-8")) \
            if (tree / "corpus" / "arguments" / f"{anchor}.json").is_file() else next(
                json.loads(p.read_text(encoding="utf-8")) for p in (tree / "corpus" / "arguments").glob("*.json")
                if json.loads(p.read_text(encoding="utf-8"))["id"] == anchor)
        statements = [record["conclusion_statement_id"], *record["premise_statement_ids"]]
        baseline = [run(["python3", "scripts/corpus.py", "related", record["conclusion_statement_id"]], tree)]
        baseline += [run(["python3", "scripts/corpus.py", "dossier", sid], tree) for sid in statements]
        context = [run(["python3", "scripts-head/corpus.py", "context", anchor], tree)]
        context_json = [run(["python3", "scripts-head/corpus.py", "context", "--json", anchor], tree)]
        return {"pr": task["pr"], "merge": merge[:12], "anchor": anchor, "needed": len(needed),
                "baseline": measure(baseline, needed), "context": measure(context, needed),
                "context_json": measure(context_json, needed)}
    finally:
        git("worktree", "remove", "--force", str(tree))


def table(rows: list[dict]) -> str:
    lines = ["| PR | anchor | needed | baseline calls/KB/s/recall | context KB/s/recall | context --json KB/recall |",
             "|---|---|---|---|---|---|"]
    for row in rows:
        b, c, j = row["baseline"], row["context"], row["context_json"]
        lines.append(f"| #{row['pr']} | `{row['anchor']}` | {row['needed']} | {b['calls']} / {b['bytes'] / 1024:.0f} / {b['seconds']} / {b['recall']:.2f} "
                     f"| {c['bytes'] / 1024:.1f} / {c['seconds']} / {c['recall']:.2f} | {j['bytes'] / 1024:.0f} / {j['recall']:.2f} |")
    return "\n".join(lines)


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--tasks", type=Path, default=TASKS)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)
    tasks = json.loads(args.tasks.read_text(encoding="utf-8"))["tasks"]
    with tempfile.TemporaryDirectory(prefix="context-benchmark-") as scratch:
        rows = [replay(task, Path(scratch)) for task in tasks]
    print(json.dumps(rows, indent=2) if args.json else table(rows))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
