"""Validated research attempts and deterministic projections of the existing corpus.

An attempt records work, never proof or closure. Dossiers consume the authoritative
frontier report; they do not maintain a second set of closure or route-cost rules.
"""
from __future__ import annotations

from datetime import date
from typing import Any
import re

ATTEMPT_KINDS = {"derivation", "refutation", "reading", "countermodel", "source-search"}
ATTEMPT_OUTCOMES = {"succeeded", "failed", "blocked", "superseded"}
PR_REFERENCE = re.compile(r"PR-[1-9][0-9]*\Z")


def validate_attempt(attempt: dict[str, Any], statements: set[str], evidence_ids: set[str]) -> None:
    """Validate local references; PR references have canonical syntax, not an online lookup."""
    if not isinstance(attempt.get("id"), str) or not re.fullmatch(r"ATTEMPT-[A-Z0-9-]+", attempt["id"]):
        raise ValueError("id must be an ATTEMPT- identifier")
    ids = attempt.get("statement_ids")
    if not isinstance(ids, list) or not ids or any(not isinstance(sid, str) or sid not in statements for sid in ids):
        raise ValueError("statement_ids must be a non-empty list of known statements")
    if len(set(ids)) != len(ids):
        raise ValueError("statement_ids must not contain duplicates")
    try:
        value = attempt.get("date")
        if not isinstance(value, str) or date.fromisoformat(value).isoformat() != value:
            raise ValueError()
    except ValueError as exc:
        raise ValueError("date must be an ISO calendar date (YYYY-MM-DD)") from exc
    if not isinstance(attempt.get("kind"), str) or attempt["kind"] not in ATTEMPT_KINDS:
        raise ValueError(f"kind must be one of {', '.join(sorted(ATTEMPT_KINDS))}")
    if not isinstance(attempt.get("outcome"), str) or attempt["outcome"] not in ATTEMPT_OUTCOMES:
        raise ValueError(f"outcome must be one of {', '.join(sorted(ATTEMPT_OUTCOMES))}")
    if not isinstance(attempt.get("summary"), str) or not attempt["summary"].strip():
        raise ValueError("summary must be a non-empty string")
    evidence = attempt.get("evidence")
    if not isinstance(evidence, list) or any(
        not isinstance(ref, str) or (ref not in evidence_ids and not PR_REFERENCE.fullmatch(ref))
        for ref in evidence
    ):
        raise ValueError("evidence must list known result/claim IDs or PR-<positive number> references")
    if len(set(evidence)) != len(evidence):
        raise ValueError("evidence must not contain duplicates")
    blocker = attempt.get("blocker")
    if blocker is not None and (not isinstance(blocker, str) or not blocker.strip()):
        raise ValueError("blocker must be a non-empty string when present")
    if attempt.get("outcome") == "blocked" and blocker is None:
        raise ValueError("blocked attempts require a blocker")


def dossier_index(data: dict[str, list[dict[str, Any]]], report: dict[str, Any]) -> dict[str, dict[str, Any]]:
    """One shared projection for CLI and explorer, including non-frontier statements."""
    statements = {entry["id"]: entry for entry in data["statements"]}
    arguments = {entry["id"]: entry for entry in data["arguments"]}
    results = {entry["id"]: entry for entry in data["results"]}
    definitions = {entry["id"]: entry for entry in data["definitions"]}
    disambiguations = data["disambiguations"]
    items = {entry["statement_id"]: entry for entry in report["items"]}
    by_statement: dict[str, dict[str, Any]] = {}
    for sid, statement in sorted(statements.items()):
        claims = [entry for entry in data["claims"] if entry["statement_id"] == sid]
        relations = [entry for entry in data["relations"] if sid in (entry["subject_id"], entry["object_id"])]
        supports = {entry["subject_id"] for entry in relations if entry["predicate"] == "supports" and entry["object_id"] == sid}
        supporting_claims = [entry for entry in data["claims"] if entry["id"] in supports]
        touching = [entry for entry in arguments.values() if sid in (
            entry["premise_statement_ids"] + entry.get("commitment_statement_ids", []) + [entry["conclusion_statement_id"]]
        )]
        # An intermediate inference output may occur without being an argument's outer premise/conclusion.
        inference_ids = {entry["id"] for entry in data["inferences"] if sid in (
            entry["input_statement_ids"] + entry.get("assumption_statement_ids", [])
            + entry.get("discharged_statement_ids", []) + [entry["output_statement_id"]]
        )}
        touching_ids = {entry["id"] for entry in touching}
        touching_ids.update(entry["id"] for entry in arguments.values() if inference_ids.intersection(entry["inference_ids"]))
        touching = [arguments[aid] for aid in sorted(touching_ids)]
        result_ids = sorted(entry["id"] for entry in results.values() if entry["argument_id"] in touching_ids)
        term_records = [statement, *claims, *supporting_claims, *touching]
        definition_ids = {did for entry in term_records for did in entry.get("definition_ids", [])}
        disambiguation_ids = {did for entry in term_records for did in entry.get("disambiguation_ids", [])}
        disambiguation_ids.update(entry["id"] for entry in disambiguations if definition_ids.intersection(entry["sense_definition_ids"]))
        # Include the senses required to read each linked disambiguation.
        definition_ids.update(did for entry in disambiguations if entry["id"] in disambiguation_ids for did in entry["sense_definition_ids"])
        attempts = sorted((entry for entry in data["attempts"] if sid in entry["statement_ids"]), key=lambda entry: (entry["date"], entry["id"]))
        transcriptions = sorted(rid for rid in result_ids if rid in report["transcription_results"])
        by_statement[sid] = {
            "statement": statement,
            "root": report["root"],
            "closure": report["closed_statements"].get(sid),
            "established": sid in report["established_statements"],
            "frontier": items.get(sid),
            "claim_ids": sorted(entry["id"] for entry in claims),
            "supporting_claim_ids": sorted(entry["id"] for entry in supporting_claims),
            "definition_ids": sorted(did for did in definition_ids if did in definitions),
            "disambiguation_ids": sorted(disambiguation_ids),
            "argument_ids": sorted(touching_ids),
            "result_ids": result_ids,
            "transcription_result_ids": transcriptions,
            "instantiation_result_ids": [rid for rid in transcriptions if report["transcription_results"][rid]["kind"] == "instantiation"],
            "alternative_relation_ids": sorted(entry["id"] for entry in relations if entry["predicate"] == "alternative_to"),
            "objection_relation_ids": sorted(entry["id"] for entry in relations if entry["predicate"] == "attacks"),
            "attempts": attempts,
            "countermodel_attempt_ids": [entry["id"] for entry in attempts if entry["kind"] == "countermodel"],
            "configuration_cases": [
                {"id": case["id"], "semantics_id": case["semantics"]["id"], "href": f"/configurations/{case['id']}",
                 "verification": "required (registration only)"}
                for case in sorted(data.get("configurations", []), key=lambda entry: entry["id"])
                if sid == case["seed_statement_id"] or sid in case["semantics"]["applications"]
            ],
            "model_evaluations": [
                {"model_id": model["id"], "vocabulary": model["vocabulary"],
                 "lean_declaration": model["lean_declaration"], "value": evaluation["value"],
                 "theorem": evaluation["theorem"],
                 "arguments": [model["bindings"][key] for key in evaluation["arguments"]]}
                for model in sorted(data.get("models", []), key=lambda entry: entry["id"])
                for evaluation in model["evaluations"] if evaluation["statement_id"] == sid
            ],
            "route_contributions": [
                {"argument_id": route["argument_id"], "cost": route["cost"],
                 "open_leaf": sid in route["open_premise_statement_ids"],
                 "direct_premise": sid in arguments[route["argument_id"]]["premise_statement_ids"]}
                for route in report["routes"]["routes"]
            ],
        }
    return by_statement


def format_dossier(dossier: dict[str, Any], data: dict[str, list[dict[str, Any]]]) -> str:
    statement = dossier["statement"]
    frontier = dossier["frontier"]
    status = dossier["closure"] or (f"open ({frontier['depth']})" if frontier else "not on the frontier")
    lines = [statement["id"], statement["paraphrase"], f"Lean: {statement.get('lean_declaration', 'none')}",
             f"Status: {status}; established: {str(dossier['established']).lower()}"]
    sections = (("claims", "claim_ids", "Source readings"), ("claims", "supporting_claim_ids", "Supporting source readings"),
                ("definitions", "definition_ids", "Definitions"), ("disambiguations", "disambiguation_ids", "Disambiguations"),
                ("relations", "alternative_relation_ids", "Alternatives"), ("relations", "objection_relation_ids", "Objections"),
                ("arguments", "argument_ids", "Arguments (premise, conclusion, commitment or inference)"),
                ("results", "result_ids", "Results"))
    for directory, key, label in sections:
        index = {entry["id"]: entry for entry in data[directory]}
        lines.append(f"\n{label}:")
        for record_id in dossier[key]:
            record = index[record_id]
            description = next((record[field] for field in ("interpretation", "definition", "resolution", "meaning", "description", "basis") if record.get(field)), "")
            if directory == "claims":
                description = f"{record['source_id']} {record['locator']}: {description}"
            if directory == "relations":
                description = f"{record['subject_id']} {record['predicate']} {record['object_id']}: {record.get('note', record.get('basis', ''))}"
            if directory == "results":
                description = f"{record.get('theorem', 'no theorem')}; {description}"
            lines.append(f"  {record_id}: {description}")
        if not dossier[key]:
            lines.append("  none recorded")
    for key, label in (("transcription_result_ids", "Transcriptions"), ("instantiation_result_ids", "Declared/recognized instantiations (not a mode-5 schema registry)")):
        lines.append(f"\n{label}: " + (", ".join(dossier[key]) or "none recorded"))
    lines.append("\nConfiguration cases (registration only; run configurations for live verification):")
    for case in dossier.get("configuration_cases", []):
        lines.append(f"  {case['id']}: semantics {case['semantics_id']}; {case['href']}")
    lines.append("\nAttempts (outcomes do not establish truth or close premises):")
    for attempt in dossier["attempts"]:
        lines.append(f"  {attempt['id']} [{attempt['date']}; {attempt['kind']}; {attempt['outcome']}]: {attempt['summary']}")
        lines.append(f"    evidence: {', '.join(attempt['evidence']) or 'none recorded'}")
        if attempt.get("blocker"):
            lines.append(f"    blocker: {attempt['blocker']}")
    if not dossier["attempts"]:
        lines.append("  none recorded")
    lines.append("\nCountermodel attempts: " + (", ".join(dossier["countermodel_attempt_ids"]) or "none recorded"))
    lines.append("Registered finite evaluations (formal interpretations only; no premise closure):")
    for evaluation in dossier["model_evaluations"]:
        lines.append(f"  {evaluation['model_id']} {evaluation['value']}; vocabulary {evaluation['vocabulary']}; {evaluation['theorem']}; arguments {evaluation['arguments']}")
    if not dossier["model_evaluations"]:
        lines.append("  none registered; no conclusion about consistency or derivability")
    lines.append("Explicit instance_of_schema registrations are recorded in corpus/relations/ (see docs/schemas.md); this dossier does not project them. No links are inferred from prose.")
    lines.append(f"\nRoutes to {dossier['root']} (one counted leaf when open_leaf=true, not a counterfactual cost reduction):")
    for route in dossier["route_contributions"]:
        lines.append(f"  {route['argument_id']}: cost={route['cost']}, open_leaf={str(route['open_leaf']).lower()}, direct_premise={str(route['direct_premise']).lower()}")
    return "\n".join(lines)
