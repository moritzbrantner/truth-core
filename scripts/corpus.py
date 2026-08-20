#!/usr/bin/env python3
"""Small, dependency-free corpus queue/validation tool for the truth-core MVP."""

from __future__ import annotations

import argparse
import json
import sys
from collections import Counter
from pathlib import Path
from typing import Any, Iterable

ROOT = Path(__file__).resolve().parents[1]
CORPUS = ROOT / "corpus"


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
        joined = ", ".join(missing)
        raise CorpusError(f"{path.relative_to(ROOT)}: missing required field(s): {joined}")


def index_by_id(records: list[tuple[Path, dict[str, Any]]], kind: str) -> dict[str, tuple[Path, dict[str, Any]]]:
    result: dict[str, tuple[Path, dict[str, Any]]] = {}
    for path, record in records:
        require(record, ["id"], path)
        record_id = record["id"]
        if not isinstance(record_id, str):
            raise CorpusError(f"{path.relative_to(ROOT)}: id must be a string")
        if record_id in result:
            other = result[record_id][0].relative_to(ROOT)
            raise CorpusError(f"{path.relative_to(ROOT)}: duplicate {kind} id {record_id}; first seen in {other}")
        result[record_id] = (path, record)
    return result


def module_path(module: str) -> Path:
    return ROOT / (module.replace(".", "/") + ".lean")


def validate() -> dict[str, int]:
    sources = load_dir("sources")
    claims = load_dir("claims")
    candidates = load_dir("candidates")
    results = load_dir("results")

    source_index = index_by_id(sources, "source")
    claim_index = index_by_id(claims, "claim")
    candidate_index = index_by_id(candidates, "candidate")
    result_index = index_by_id(results, "result")

    for path, source in sources:
        require(source, ["id", "kind", "author", "work", "citation_system", "work_urn", "catalog_url"], path)

    all_lean = "\n".join(
        path.read_text(encoding="utf-8") for path in sorted((ROOT / "TruthCore").rglob("*.lean"))
    )

    for path, claim in claims:
        require(claim, ["id", "source_id", "locator", "interpretation", "paraphrase", "lean_declaration", "status"], path)
        if claim["source_id"] not in source_index:
            raise CorpusError(f"{path.relative_to(ROOT)}: unknown source_id {claim['source_id']}")
        if claim["status"] != "formalized":
            raise CorpusError(f"{path.relative_to(ROOT)}: claim status must be 'formalized' in the MVP")
        parent = claim.get("interpretation_of")
        if parent is not None and parent not in claim_index:
            raise CorpusError(f"{path.relative_to(ROOT)}: unknown interpretation_of claim {parent}")
        declaration = claim["lean_declaration"]
        tail = declaration.rsplit(".", 1)[-1]
        if tail not in all_lean:
            raise CorpusError(f"{path.relative_to(ROOT)}: Lean declaration tail {tail!r} was not found under TruthCore/")

    for path, candidate in candidates:
        require(candidate, ["id", "source_id", "locator", "priority", "goal", "reason", "status"], path)
        if candidate["source_id"] not in source_index:
            raise CorpusError(f"{path.relative_to(ROOT)}: unknown source_id {candidate['source_id']}")
        if candidate["status"] != "candidate":
            raise CorpusError(f"{path.relative_to(ROOT)}: candidate status must be 'candidate'")
        if not isinstance(candidate["priority"], int):
            raise CorpusError(f"{path.relative_to(ROOT)}: priority must be an integer")

    for path, result in results:
        require(result, ["id", "claim_ids", "challenge_module", "solution_module", "theorem", "comparator_config", "status", "meaning"], path)
        for claim_id in result["claim_ids"]:
            if claim_id not in claim_index:
                raise CorpusError(f"{path.relative_to(ROOT)}: unknown claim id {claim_id}")
        challenge = module_path(result["challenge_module"])
        solution = module_path(result["solution_module"])
        config_path = ROOT / result["comparator_config"]
        for expected in (challenge, solution, config_path):
            if not expected.is_file():
                raise CorpusError(f"{path.relative_to(ROOT)}: referenced file does not exist: {expected.relative_to(ROOT)}")
        try:
            config = json.loads(config_path.read_text(encoding="utf-8"))
        except json.JSONDecodeError as exc:
            raise CorpusError(f"{config_path.relative_to(ROOT)}: invalid Comparator JSON: {exc}") from exc
        if config.get("challenge_module") != result["challenge_module"]:
            raise CorpusError(f"{config_path.relative_to(ROOT)}: challenge module disagrees with result record")
        if config.get("solution_module") != result["solution_module"]:
            raise CorpusError(f"{config_path.relative_to(ROOT)}: solution module disagrees with result record")
        if result["theorem"] not in config.get("theorem_names", []):
            raise CorpusError(f"{config_path.relative_to(ROOT)}: theorem is not listed in theorem_names")
        if config.get("permitted_axioms") != []:
            raise CorpusError(f"{config_path.relative_to(ROOT)}: seed results must require no permitted axioms")
        if config.get("enable_nanoda") is not True:
            raise CorpusError(f"{config_path.relative_to(ROOT)}: NanoDa must be enabled")

    cross_ids = list(candidate_index) + list(result_index)
    duplicates = [value for value, count in Counter(cross_ids).items() if count > 1]
    if duplicates:
        raise CorpusError(f"candidate/result id collision(s): {', '.join(sorted(duplicates))}")

    return {"sources": len(source_index), "claims": len(claim_index), "candidates": len(candidate_index), "results": len(result_index)}


def command_check(_: argparse.Namespace) -> int:
    counts = validate()
    print("corpus ok: " f"{counts['sources']} sources, {counts['claims']} claims, " f"{counts['results']} results, {counts['candidates']} candidates")
    return 0


def command_status(_: argparse.Namespace) -> int:
    counts = validate()
    print(f"sources:    {counts['sources']}")
    print(f"claims:     {counts['claims']}")
    print(f"results:    {counts['results']}")
    print(f"candidates: {counts['candidates']}")
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


def command_results(_: argparse.Namespace) -> int:
    validate()
    for _, result in load_dir("results"):
        print(result["id"])
    return 0


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description="Inspect and validate the truth-core corpus")
    sub = result.add_subparsers(dest="command", required=True)
    sub.add_parser("check", help="validate corpus references and Comparator configs").set_defaults(func=command_check)
    sub.add_parser("status", help="show corpus counts").set_defaults(func=command_status)
    sub.add_parser("next", help="print the highest-priority Codex work item").set_defaults(func=command_next)
    sub.add_parser("results", help="print result IDs, one per line").set_defaults(func=command_results)
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
