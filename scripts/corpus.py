#!/usr/bin/env python3
"""Small, dependency-free corpus queue/validation tool for truth-core."""

from __future__ import annotations

import argparse
import json
import sys
from collections import Counter
from pathlib import Path
from typing import Any, Iterable

from source_evidence import SourceEvidenceError, validate_bindings

ROOT = Path(__file__).resolve().parents[1]
CORPUS = ROOT / "corpus"
ENTITY_KINDS = {"source", "statement", "claim", "inference", "argument"}


class CorpusError(Exception):
    pass


def load_dir(name: str) -> list[tuple[Path, dict[str, Any]]]:
    directory = CORPUS / name
    records: list[tuple[Path, dict[str, Any]]] = []
    for path in sorted(directory.glob("*.json")):
        try:
            data = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as exc:
            raise CorpusError(f"{path.relative_to(ROOT)}: cannot read JSON: {exc}") from exc
        if not isinstance(data, dict):
            raise CorpusError(f"{path.relative_to(ROOT)}: top-level JSON value must be an object")
        records.append((path, data))
    return records


def require(record: dict[str, Any], fields: Iterable[str], path: Path) -> None:
    missing = [field for field in fields if record.get(field) in (None, "", [])]
    if missing:
        raise CorpusError(f"{path.relative_to(ROOT)}: missing required field(s): {', '.join(missing)}")


def require_string_list(
    record: dict[str, Any],
    field: str,
    path: Path,
    *,
    allow_empty: bool = True,
) -> list[str]:
    value = record.get(field)
    if not isinstance(value, list) or any(not isinstance(item, str) or not item for item in value):
        raise CorpusError(f"{path.relative_to(ROOT)}: {field} must be a list of non-empty strings")
    if not allow_empty and not value:
        raise CorpusError(f"{path.relative_to(ROOT)}: {field} must not be empty")
    return value


def index_by_id(
    records: list[tuple[Path, dict[str, Any]]],
    kind: str,
) -> dict[str, tuple[Path, dict[str, Any]]]:
    result: dict[str, tuple[Path, dict[str, Any]]] = {}
    for path, record in records:
        require(record, ["id"], path)
        record_id = record["id"]
        if not isinstance(record_id, str):
            raise CorpusError(f"{path.relative_to(ROOT)}: id must be a string")
        if record_id in result:
            other = result[record_id][0].relative_to(ROOT)
            raise CorpusError(
                f"{path.relative_to(ROOT)}: duplicate {kind} id {record_id}; first seen in {other}"
            )
        result[record_id] = (path, record)
    return result


def module_path(module: str) -> Path:
    return ROOT / (module.replace(".", "/") + ".lean")


def validate_argument_derivation(
    path: Path,
    argument: dict[str, Any],
    inference_index: dict[str, tuple[Path, dict[str, Any]]],
) -> None:
    available = set(argument["premise_statement_ids"])
    remaining = {
        inference_id: inference_index[inference_id][1]
        for inference_id in argument["inference_ids"]
    }

    while remaining:
        progressed = False
        for inference_id, inference in list(remaining.items()):
            scoped = set(inference["assumption_statement_ids"])
            if set(inference["input_statement_ids"]).issubset(available | scoped):
                available.add(inference["output_statement_id"])
                del remaining[inference_id]
                progressed = True
        if not progressed:
            blocked = ", ".join(sorted(remaining))
            raise CorpusError(
                f"{path.relative_to(ROOT)}: inference applications are not grounded "
                f"in advertised premises: {blocked}"
            )

    if argument["conclusion_statement_id"] not in available:
        raise CorpusError(
            f"{path.relative_to(ROOT)}: conclusion is not derivable from the listed inference applications"
        )


def validate() -> dict[str, int]:
    sources = load_dir("sources")
    statements = load_dir("statements")
    claims = load_dir("claims")
    inferences = load_dir("inferences")
    arguments = load_dir("arguments")
    relations = load_dir("relations")
    candidates = load_dir("candidates")
    results = load_dir("results")

    source_index = index_by_id(sources, "source")
    statement_index = index_by_id(statements, "statement")
    claim_index = index_by_id(claims, "claim")
    inference_index = index_by_id(inferences, "inference")
    argument_index = index_by_id(arguments, "argument")
    relation_index = index_by_id(relations, "relation")
    candidate_index = index_by_id(candidates, "candidate")
    result_index = index_by_id(results, "result")

    for path, source in sources:
        require(
            source,
            ["id", "kind", "author", "work", "citation_system", "work_urn", "catalog_url"],
            path,
        )

    try:
        passage_count, bound_claim_count = validate_bindings()
    except SourceEvidenceError as exc:
        raise CorpusError(str(exc)) from exc
    if bound_claim_count != len(claim_index):
        raise CorpusError(
            f"source evidence bound {bound_claim_count} claims but corpus contains {len(claim_index)}"
        )

    all_lean = "\n".join(
        path.read_text(encoding="utf-8")
        for path in sorted((ROOT / "TruthCore").rglob("*.lean"))
    )

    for path, statement in statements:
        require(statement, ["id", "paraphrase"], path)
        declaration = statement.get("lean_declaration")
        if declaration is not None:
            if not isinstance(declaration, str) or not declaration:
                raise CorpusError(
                    f"{path.relative_to(ROOT)}: lean_declaration must be a non-empty string when present"
                )
            tail = declaration.rsplit(".", 1)[-1]
            if tail not in all_lean:
                raise CorpusError(
                    f"{path.relative_to(ROOT)}: Lean declaration tail {tail!r} "
                    "was not found under TruthCore/"
                )

    for path, claim in claims:
        require(
            claim,
            ["id", "statement_id", "source_id", "locator", "interpretation", "status"],
            path,
        )
        if claim["statement_id"] not in statement_index:
            raise CorpusError(
                f"{path.relative_to(ROOT)}: unknown statement_id {claim['statement_id']}"
            )
        if claim["source_id"] not in source_index:
            raise CorpusError(
                f"{path.relative_to(ROOT)}: unknown source_id {claim['source_id']}"
            )
        if claim["status"] != "formalized":
            raise CorpusError(
                f"{path.relative_to(ROOT)}: claim status must be 'formalized' in the MVP"
            )
        parent = claim.get("interpretation_of")
        if parent is not None and parent not in claim_index:
            raise CorpusError(
                f"{path.relative_to(ROOT)}: unknown interpretation_of claim {parent}"
            )

    for path, inference in inferences:
        require(
            inference,
            ["id", "input_statement_ids", "output_statement_id", "rule", "meaning"],
            path,
        )
        inputs = require_string_list(inference, "input_statement_ids", path, allow_empty=False)
        assumptions = require_string_list(inference, "assumption_statement_ids", path)
        discharges = require_string_list(inference, "discharged_statement_ids", path)
        for statement_id in [
            *inputs,
            *assumptions,
            *discharges,
            inference["output_statement_id"],
        ]:
            if statement_id not in statement_index:
                raise CorpusError(
                    f"{path.relative_to(ROOT)}: unknown statement id {statement_id}"
                )
        if not set(discharges).issubset(set(assumptions)):
            raise CorpusError(
                f"{path.relative_to(ROOT)}: discharged assumptions must also be listed "
                "as scoped assumptions"
            )

    for path, argument in arguments:
        require(
            argument,
            ["id", "premise_statement_ids", "conclusion_statement_id", "inference_ids", "meaning"],
            path,
        )
        premises = require_string_list(argument, "premise_statement_ids", path, allow_empty=False)
        inference_ids = require_string_list(argument, "inference_ids", path, allow_empty=False)
        for statement_id in [*premises, argument["conclusion_statement_id"]]:
            if statement_id not in statement_index:
                raise CorpusError(
                    f"{path.relative_to(ROOT)}: unknown statement id {statement_id}"
                )
        for inference_id in inference_ids:
            if inference_id not in inference_index:
                raise CorpusError(
                    f"{path.relative_to(ROOT)}: unknown inference id {inference_id}"
                )
        validate_argument_derivation(path, argument, inference_index)

    entity_indexes = {
        "source": source_index,
        "statement": statement_index,
        "claim": claim_index,
        "inference": inference_index,
        "argument": argument_index,
    }
    for path, relation in relations:
        require(
            relation,
            ["id", "subject_kind", "subject_id", "predicate", "object_kind", "object_id"],
            path,
        )
        for side in ("subject", "object"):
            kind = relation[f"{side}_kind"]
            entity_id = relation[f"{side}_id"]
            if kind not in ENTITY_KINDS:
                raise CorpusError(f"{path.relative_to(ROOT)}: unknown {side}_kind {kind}")
            if entity_id not in entity_indexes[kind]:
                raise CorpusError(
                    f"{path.relative_to(ROOT)}: unknown {side} {kind} id {entity_id}"
                )

    for path, candidate in candidates:
        require(
            candidate,
            ["id", "source_id", "locator", "priority", "goal", "reason", "status"],
            path,
        )
        if candidate["source_id"] not in source_index:
            raise CorpusError(
                f"{path.relative_to(ROOT)}: unknown source_id {candidate['source_id']}"
            )
        if candidate["status"] != "candidate":
            raise CorpusError(
                f"{path.relative_to(ROOT)}: candidate status must be 'candidate'"
            )
        if not isinstance(candidate["priority"], int):
            raise CorpusError(
                f"{path.relative_to(ROOT)}: priority must be an integer"
            )

    for path, result in results:
        require(
            result,
            [
                "id",
                "argument_id",
                "challenge_module",
                "solution_module",
                "theorem",
                "comparator_config",
                "status",
            ],
            path,
        )
        if result["argument_id"] not in argument_index:
            raise CorpusError(
                f"{path.relative_to(ROOT)}: unknown argument_id {result['argument_id']}"
            )
        challenge = module_path(result["challenge_module"])
        solution = module_path(result["solution_module"])
        config_path = ROOT / result["comparator_config"]
        for expected in (challenge, solution, config_path):
            if not expected.is_file():
                raise CorpusError(
                    f"{path.relative_to(ROOT)}: referenced file does not exist: "
                    f"{expected.relative_to(ROOT)}"
                )
        try:
            config = json.loads(config_path.read_text(encoding="utf-8"))
        except json.JSONDecodeError as exc:
            raise CorpusError(
                f"{config_path.relative_to(ROOT)}: invalid Comparator JSON: {exc}"
            ) from exc
        if config.get("challenge_module") != result["challenge_module"]:
            raise CorpusError(
                f"{config_path.relative_to(ROOT)}: challenge module disagrees with result record"
            )
        if config.get("solution_module") != result["solution_module"]:
            raise CorpusError(
                f"{config_path.relative_to(ROOT)}: solution module disagrees with result record"
            )
        if result["theorem"] not in config.get("theorem_names", []):
            raise CorpusError(
                f"{config_path.relative_to(ROOT)}: theorem is not listed in theorem_names"
            )
        if config.get("permitted_axioms") != []:
            raise CorpusError(
                f"{config_path.relative_to(ROOT)}: seed results must require no permitted axioms"
            )
        if config.get("enable_nanoda") is not True:
            raise CorpusError(
                f"{config_path.relative_to(ROOT)}: NanoDa must be enabled"
            )

    cross_ids = list(candidate_index) + list(result_index)
    duplicates = [value for value, count in Counter(cross_ids).items() if count > 1]
    if duplicates:
        raise CorpusError(
            f"candidate/result id collision(s): {', '.join(sorted(duplicates))}"
        )

    return {
        "sources": len(source_index),
        "passages": passage_count,
        "statements": len(statement_index),
        "claims": len(claim_index),
        "inferences": len(inference_index),
        "arguments": len(argument_index),
        "relations": len(relation_index),
        "candidates": len(candidate_index),
        "results": len(result_index),
    }


def command_check(_: argparse.Namespace) -> int:
    counts = validate()
    print(
        "corpus ok: "
        f"{counts['sources']} sources, {counts['passages']} passages, "
        f"{counts['statements']} statements, {counts['claims']} claims, "
        f"{counts['inferences']} inferences, {counts['arguments']} arguments, "
        f"{counts['relations']} relations, {counts['results']} results, "
        f"{counts['candidates']} candidates"
    )
    return 0


def command_status(_: argparse.Namespace) -> int:
    counts = validate()
    for key in (
        "sources",
        "passages",
        "statements",
        "claims",
        "inferences",
        "arguments",
        "relations",
        "results",
        "candidates",
    ):
        print(f"{key + ':':12} {counts[key]}")
    return 0


def command_next(_: argparse.Namespace) -> int:
    validate()
    candidates = load_dir("candidates")
    if not candidates:
        print("no candidates")
        return 1
    _, candidate = min(candidates, key=lambda item: (item[1]["priority"], item[1]["id"]))
    print(json.dumps(candidate, indent=2, ensure_ascii=False))
    return 0


def command_ids(directory: str):
    def command(_: argparse.Namespace) -> int:
        validate()
        for _, record in load_dir(directory):
            print(record["id"])
        return 0

    return command


# --- bind-check (#162): argument JSON must match the Lean theorem type -------

BIND_TOOL = ROOT / "scripts" / "BindTypes.lean"


def bind_tool_input(results: list[tuple[Path, dict[str, Any]]]) -> dict[str, list[str]]:
    """The modules to import and the theorems to describe, in result-id order."""
    ordered = sorted((record for _, record in results), key=lambda record: record["id"])
    return {
        "modules": sorted({record["solution_module"] for record in ordered}),
        "theorems": [record["theorem"] for record in ordered],
    }


def run_bind_tool(tool_input: dict[str, list[str]]) -> list[dict[str, Any]]:
    """Run scripts/BindTypes.lean against the built library (needs `lake build`)."""
    import subprocess
    import tempfile

    with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False, encoding="utf-8") as handle:
        json.dump(tool_input, handle)
        input_path = handle.name
    try:
        completed = subprocess.run(
            ["lake", "env", "lean", "--run", str(BIND_TOOL), input_path],
            cwd=ROOT,
            capture_output=True,
            text=True,
            check=False,
        )
    except FileNotFoundError as exc:
        raise CorpusError("bind-check needs `lake` on PATH (run after `lake build`)") from exc
    finally:
        Path(input_path).unlink(missing_ok=True)
    if completed.returncode != 0:
        raise CorpusError(
            f"{BIND_TOOL.relative_to(ROOT)} failed (exit {completed.returncode}):\n"
            f"{completed.stderr.strip() or completed.stdout.strip()}"
        )
    try:
        described = json.loads(completed.stdout)
    except json.JSONDecodeError as exc:
        raise CorpusError(f"{BIND_TOOL.relative_to(ROOT)} printed invalid JSON: {exc}") from exc
    if not isinstance(described, list):
        raise CorpusError(f"{BIND_TOOL.relative_to(ROOT)} must print a JSON array")
    return described


def is_corpus_constant(name: str | None) -> bool:
    return isinstance(name, str) and (name == "TruthCore" or name.startswith("TruthCore."))


def bind_result(
    result: dict[str, Any],
    argument: dict[str, Any],
    statement_index: dict[str, tuple[Path, dict[str, Any]]],
    described: dict[str, Any],
) -> dict[str, Any]:
    """Compare one result's argument record with the Lean description of its theorem.

    A binder whose type lives in `Prop` is a premise hypothesis; every other
    binder (`Type`/`Sort` parameters, predicates, individuals) is vocabulary.
    A premise or conclusion statement binds to a hypothesis or result type by
    equality of its `lean_declaration` with the type's head constant.

    A statement without `lean_declaration` cannot be bound by head constant.
    It is matched to a type whose head is not a `TruthCore` declaration (a
    logical form such as `∃ x, …` over vocabulary) and reported as
    `undecidable`; if the type's head is a `TruthCore` declaration, the
    statement should name it, and that is a mismatch.
    """

    def declaration(statement_id: str) -> str | None:
        return statement_index[statement_id][1].get("lean_declaration")

    problems: list[dict[str, Any]] = []
    undecidable: list[dict[str, Any]] = []
    if "error" in described:
        problems.append({"kind": "lean-error", "detail": described["error"]})
        return {
            "id": result["id"],
            "theorem": result["theorem"],
            "status": "mismatch",
            "premises": [],
            "conclusion": None,
            "parameters": [],
            "problems": problems,
            "undecidable": [],
        }

    binders = described.get("binders", [])
    parameters = [binder["name"] for binder in binders if not binder["prop"]]
    hypotheses = [dict(binder, position=index) for index, binder in enumerate(binders) if binder["prop"]]

    unused = list(argument["premise_statement_ids"])
    premises: list[dict[str, Any]] = []
    unmatched: list[dict[str, Any]] = []
    # First pass: bind by head constant.
    for hypothesis in hypotheses:
        match = next(
            (sid for sid in unused if declaration(sid) is not None and declaration(sid) == hypothesis["head"]),
            None,
        )
        if match is None:
            unmatched.append(hypothesis)
            continue
        unused.remove(match)
        premises.append(
            {
                "hypothesis": hypothesis["name"],
                "position": hypothesis["position"],
                "statement_id": match,
                "lean_declaration": hypothesis["head"],
            }
        )
    # Second pass: statements without a declaration take logical-form hypotheses.
    for hypothesis in unmatched:
        match = None
        if not is_corpus_constant(hypothesis["head"]):
            match = next((sid for sid in unused if declaration(sid) is None), None)
        if match is None:
            problems.append(
                {
                    "kind": "extra-hypothesis",
                    "hypothesis": hypothesis["name"],
                    "position": hypothesis["position"],
                    "head": hypothesis["head"],
                    "type": hypothesis["type"],
                }
            )
            continue
        unused.remove(match)
        premises.append(
            {
                "hypothesis": hypothesis["name"],
                "position": hypothesis["position"],
                "statement_id": match,
                "lean_declaration": None,
            }
        )
        undecidable.append(
            {
                "role": "premise",
                "statement_id": match,
                "hypothesis": hypothesis["name"],
                "position": hypothesis["position"],
                "type": hypothesis["type"],
            }
        )
    for statement_id in unused:
        problems.append(
            {"kind": "missing-premise", "statement_id": statement_id, "lean_declaration": declaration(statement_id)}
        )

    conclusion_id = argument["conclusion_statement_id"]
    expected = declaration(conclusion_id)
    outcome = described["result"]
    conclusion = {"statement_id": conclusion_id, "lean_declaration": outcome["head"], "type": outcome["type"]}
    if not outcome["prop"]:
        problems.append({"kind": "conclusion-not-prop", "type": outcome["type"]})
    elif expected is not None:
        if expected != outcome["head"]:
            problems.append(
                {
                    "kind": "conclusion-mismatch",
                    "statement_id": conclusion_id,
                    "lean_declaration": expected,
                    "head": outcome["head"],
                    "type": outcome["type"],
                }
            )
    elif is_corpus_constant(outcome["head"]):
        problems.append(
            {
                "kind": "conclusion-unbound-declaration",
                "statement_id": conclusion_id,
                "head": outcome["head"],
                "type": outcome["type"],
            }
        )
    else:
        conclusion["lean_declaration"] = None
        undecidable.append({"role": "conclusion", "statement_id": conclusion_id, "type": outcome["type"]})

    if problems:
        status = "mismatch"
    elif undecidable:
        status = "undecidable"
    else:
        status = "bound"
    premises.sort(key=lambda entry: entry["position"])
    return {
        "id": result["id"],
        "theorem": result["theorem"],
        "status": status,
        "premises": [dict(sorted(entry.items())) for entry in premises],
        "conclusion": dict(sorted(conclusion.items())),
        "parameters": parameters,
        "problems": problems,
        "undecidable": undecidable,
    }


def bind_report(described_list: list[dict[str, Any]]) -> dict[str, Any]:
    """Bind every result against the Lean descriptions (keyed by theorem name)."""
    statement_index = index_by_id(load_dir("statements"), "statement")
    argument_index = index_by_id(load_dir("arguments"), "argument")
    results = load_dir("results")
    by_theorem = {entry.get("theorem"): entry for entry in described_list}
    entries = []
    for _, result in sorted(results, key=lambda item: item[1]["id"]):
        described = by_theorem.get(result["theorem"], {"error": "theorem not described by the Lean tool"})
        argument = argument_index[result["argument_id"]][1]
        entries.append(bind_result(result, argument, statement_index, described))
    summary = Counter(entry["status"] for entry in entries)
    return {
        "summary": {status: summary.get(status, 0) for status in ("bound", "undecidable", "mismatch")},
        "results": entries,
    }


def command_bind_check(args: argparse.Namespace) -> int:
    validate()
    if args.lean_json:
        described_list = json.loads(Path(args.lean_json).read_text(encoding="utf-8"))
    else:
        described_list = run_bind_tool(bind_tool_input(load_dir("results")))
    report = bind_report(described_list)
    if args.json:
        print(json.dumps(report, indent=2, ensure_ascii=False, sort_keys=True))
    else:
        for entry in report["results"]:
            for item in entry["undecidable"]:
                print(
                    f"undecidable: {entry['id']}: {item['role']} {item['statement_id']} "
                    f"has no lean_declaration; Lean type is `{item['type']}`"
                )
            for problem in entry["problems"]:
                print(f"mismatch: {entry['id']}: {json.dumps(problem, ensure_ascii=False, sort_keys=True)}")
        summary = report["summary"]
        print(
            f"bind-check: {summary['bound']} bound, {summary['undecidable']} undecidable, "
            f"{summary['mismatch']} mismatch"
        )
    return 1 if report["summary"]["mismatch"] else 0


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description="Inspect and validate the truth-core corpus")
    sub = result.add_subparsers(dest="command", required=True)
    sub.add_parser("check", help="validate corpus references, source evidence, and Comparator configs").set_defaults(
        func=command_check
    )
    sub.add_parser("status", help="show corpus counts").set_defaults(func=command_status)
    sub.add_parser("next", help="print the highest-priority Codex work item").set_defaults(
        func=command_next
    )
    sub.add_parser("arguments", help="print argument IDs, one per line").set_defaults(
        func=command_ids("arguments")
    )
    sub.add_parser("results", help="print verification result IDs, one per line").set_defaults(
        func=command_ids("results")
    )
    bind = sub.add_parser(
        "bind-check",
        help="check that argument premises/conclusions match each result theorem's Lean type (after lake build)",
    )
    bind.add_argument("--json", action="store_true", help="print the full deterministic binding report")
    bind.add_argument("--lean-json", help="use a saved scripts/BindTypes.lean output instead of running Lean")
    bind.set_defaults(func=command_bind_check)
    return result


def main() -> int:
    args = parser().parse_args()
    try:
        return args.func(args)
    except CorpusError as exc:
        print(f"corpus error: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
