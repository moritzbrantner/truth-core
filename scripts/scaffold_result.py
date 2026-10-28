#!/usr/bin/env python3
"""Preview linked result drafts for existing statements; never certify a proof."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import sys

import corpus


def bundle(args: argparse.Namespace) -> dict:
    """Build drafts from authoritative statements, optionally comparing saved types."""
    if not re.fullmatch(r"[A-Z][A-Z0-9]*(?:-[A-Z0-9]+)*", args.id):
        raise corpus.CorpusError("--id must be an uppercase hyphenated identifier")
    for name in (args.challenge_module, args.solution_module, args.theorem):
        if not re.fullmatch(r"TruthCore(?:\.[A-Za-z_][A-Za-z0-9_]*)+", name):
            raise corpus.CorpusError(f"unsupported Lean name: {name}")
    if not args.challenge_module.endswith(".Challenge") or not args.solution_module.endswith(".Solution"):
        raise corpus.CorpusError("module names must end in .Challenge and .Solution")
    meaning = args.meaning_file.read_text(encoding="utf-8").strip()
    if not meaning or not args.rule.strip():
        raise corpus.CorpusError("meaning and inference rule must be supplied explicitly")
    if len(args.premise) != len(set(args.premise)):
        raise corpus.CorpusError("duplicate premise IDs: use distinct statement roles explicitly")
    statements = corpus.index_by_id(corpus.load_dir("statements"), "statement")
    selected = [*args.premise, args.conclusion]
    for sid in selected:
        if sid not in statements:
            raise corpus.CorpusError(f"unknown statement: {sid}")
        if not statements[sid][1].get("lean_declaration"):
            raise corpus.CorpusError(f"statement has no authoritative lean_declaration: {sid}")
    inference_id = f"INF-{args.id}"
    for directory, record_id in (("inferences", inference_id), ("arguments", args.id), ("results", args.id)):
        if record_id in corpus.index_by_id(corpus.load_dir(directory), directory):
            raise corpus.CorpusError(f"existing {directory} ID: {record_id}")
    slug = args.id.lower()
    config_path = f"results/{args.id}/comparator.json"
    result = {
        "id": args.id, "argument_id": args.id,
        "challenge_module": args.challenge_module, "solution_module": args.solution_module,
        "theorem": args.theorem, "comparator_config": config_path,
        "description": meaning,
    }
    # Deliberately omit required status: this is not a ready-to-register result.
    argument = {
        "id": args.id, "premise_statement_ids": args.premise,
        "conclusion_statement_id": args.conclusion, "inference_ids": [inference_id],
        "meaning": meaning,
    }
    for field in ("definition_ids", "disambiguation_ids"):
        links = sorted({link for sid in selected for link in statements[sid][1].get(field, [])})
        if links:
            argument[field] = links
    inference = {
        "id": inference_id, "input_statement_ids": args.premise,
        "output_statement_id": args.conclusion, "rule": args.rule,
        "meaning": meaning, "assumption_statement_ids": [], "discharged_statement_ids": [],
    }
    config = {
        "challenge_module": args.challenge_module, "solution_module": args.solution_module,
        "theorem_names": [args.theorem], "permitted_axioms": sorted(set(args.axiom)),
        "enable_nanoda": True,
    }
    error = corpus.permitted_axioms_error(config)
    if error:
        raise corpus.CorpusError(error)
    records = {
        f"corpus/inferences/{slug}.json": inference,
        f"corpus/arguments/{args.id}.json": argument,
        f"corpus/results/{args.id}.json": result,
        config_path: config,
    }
    for path in records:
        if (corpus.ROOT / path).exists():
            raise corpus.CorpusError(f"canonical path already exists: {path}")
    binding = None
    if args.type_evidence:
        raw = args.type_evidence.read_bytes()
        descriptions = json.loads(raw)
        if not isinstance(descriptions, list):
            raise corpus.CorpusError("--type-evidence expects the JSON array exported by BindTypes.lean")
        matches = [item for item in descriptions if isinstance(item, dict) and item.get("theorem") == args.theorem]
        if len(matches) != 1:
            raise corpus.CorpusError("type evidence must contain the requested theorem exactly once")
        try:
            report = corpus.bind_result(result, argument, statements, matches[0], pins={})
        except (KeyError, TypeError, AttributeError) as exc:
            raise corpus.CorpusError(f"malformed BindTypes description: {exc}") from exc
        if report["status"] != "bound":
            raise corpus.CorpusError(f"supplied type evidence does not bind: {json.dumps(report['problems'])}")
        binding = {"sha256": hashlib.sha256(raw).hexdigest(), "report": report}
    return {
        "notice": "DRAFT ONLY. No Lean, source, axiom, Comparator or NanoDa verification was run.",
        "existing_statements": [
            {"id": sid, "path": str(statements[sid][0].relative_to(corpus.ROOT)),
             "lean_declaration": statements[sid][1]["lean_declaration"]}
            for sid in dict.fromkeys(selected)
        ],
        "supplied_type_comparison": binding,
        "remaining": [
            "Review the supplied meaning against the Lean type and source evidence; inspect premise dossiers.",
            "Review inherited definition/disambiguation links, scoped assumptions and transcription classification.",
            "Freeze Challenge before constructing Solution; this command creates neither Lean file.",
            "Complete required result status only after the corresponding workflow step; never copy the manifest into corpus.",
            "Run required final binding, axiom, Comparator, NanoDa and repository gates on final inputs.",
        ],
        "records": records,
    }


def write_drafts(output: Path, draft: dict) -> None:
    """A new directory only: an existing destination is never touched."""
    output = output.resolve()
    for protected in (corpus.ROOT, corpus.CORPUS, corpus.ROOT / "results", corpus.ROOT / "TruthCore"):
        if output == protected or (protected != corpus.ROOT and protected in output.parents):
            raise corpus.CorpusError("output must be a separate draft directory, outside canonical record/module trees")
    output.mkdir(parents=True, exist_ok=False)
    for relative, record in draft["records"].items():
        path = output / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        with path.open("x", encoding="utf-8") as handle:
            handle.write(json.dumps(record, indent=2, ensure_ascii=False) + "\n")
    manifest = {key: value for key, value in draft.items() if key != "records"}
    manifest["canonical_paths"] = list(draft["records"])
    with (output / "manifest.json").open("x", encoding="utf-8") as handle:
        handle.write(json.dumps(manifest, indent=2, ensure_ascii=False) + "\n")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--id", required=True, help="new shared argument/result ID; inference is INF-ID")
    parser.add_argument("--premise", action="append", default=[], help="existing statement ID (repeat; omitted means no premises)")
    parser.add_argument("--conclusion", required=True, help="existing statement ID")
    parser.add_argument("--meaning-file", type=Path, required=True, help="reviewed prose used verbatim in the three records")
    parser.add_argument("--rule", required=True, help="explicit inference rule label")
    parser.add_argument("--challenge-module", required=True)
    parser.add_argument("--solution-module", required=True)
    parser.add_argument("--theorem", required=True)
    parser.add_argument("--axiom", action="append", default=[], choices=["propext", "Classical.choice", "Quot.sound"], help="explicit permission only; default none, no axiom inspection")
    parser.add_argument("--type-evidence", type=Path, help="optional existing BindTypes.lean output; compared as supplied, never trusted as fresh verification")
    parser.add_argument("--output-dir", type=Path, help="create a NEW draft directory; default prints the bundle to stdout")
    args = parser.parse_args()
    try:
        draft = bundle(args)
        if args.output_dir:
            write_drafts(args.output_dir, draft)
            print(f"Drafts written to {args.output_dir}; result status is intentionally unset.")
        else:
            print(json.dumps(draft, indent=2, ensure_ascii=False))
    except (corpus.CorpusError, OSError, ValueError) as exc:
        parser.exit(2, f"scaffold_result: {exc}\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
