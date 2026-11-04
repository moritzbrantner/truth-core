"""Bounded cross-result research experiments, derived from the registered corpus.

This is a discovery view, not an entailment checker or a new research registry.
An exact Lean Solution import witnesses *reuse*, but never certifies that two
results describe the same semantic interpretation. Callers must select one
concrete profile module, inspect types and keep witness identity fixed.
"""
from __future__ import annotations

from functools import lru_cache
from pathlib import Path
import re
from typing import Any

from argument_context import import_closure, lean_imports, module_path


LEAN_MODULE = re.compile(r"^TruthCore(?:\.[A-Za-z][A-Za-z0-9_]*)+$")
SCOPE_FIELDS = ("semantic_profile_id", "model_profile_id", "witness_id")


def experiment_report(
    root: Path,
    data: dict[str, list[dict[str, Any]]],
    frontier: dict[str, Any],
    anchor_id: str,
    profile_module: str,
    *,
    limit: int = 5,
) -> dict[str, Any]:
    """Find *recorded* unresolved joins where one Solution imports another.

    Requiring one named profile module and a direct imported Solution makes the
    candidate set conservative. Import proximity is not a semantic-type check;
    the requested experiment is precisely to test a common instantiation.
    """
    results = {record["id"]: record for record in data["results"]}
    arguments = {record["id"]: record for record in data["arguments"]}
    statements = {record["id"]: record for record in data["statements"]}
    if anchor_id not in results:
        raise ValueError(f"unknown result: {anchor_id}")
    if not LEAN_MODULE.fullmatch(profile_module) or not module_path(root, profile_module).is_file():
        raise ValueError(f"unknown or invalid profile module: {profile_module}")
    if not 1 <= limit <= 20:
        raise ValueError("limit must be between 1 and 20")

    @lru_cache(maxsize=None)
    def imports(module: str) -> frozenset[str]:
        return frozenset(lean_imports(root, module))

    @lru_cache(maxsize=None)
    def closure(module: str) -> frozenset[str]:
        return frozenset(import_closure(root, module))

    def in_profile(result: dict[str, Any]) -> bool:
        module = result.get("solution_module")
        return bool(module and module_path(root, module).is_file() and
                    (module == profile_module or profile_module in closure(module)))

    anchor = results[anchor_id]
    if not in_profile(anchor):
        raise ValueError(f"anchor result {anchor_id} does not import selected profile {profile_module}")

    def scope_compatible(left: dict[str, Any], right: dict[str, Any]) -> bool:
        # Optional exact metadata is a veto, not a source of inferred identity.
        # Missing metadata still requires human review of the actual Lean types.
        return all(left.get(field) == right.get(field)
                   for field in SCOPE_FIELDS
                   if field in left or field in right)

    def direct_edge(peer: dict[str, Any]) -> dict[str, str] | None:
        source = peer.get("solution_module")
        target = anchor.get("solution_module")
        if not source or not target or source == target:
            return None
        if source in imports(target):
            return {"consumer_result_id": anchor_id, "imported_result_id": peer["id"]}
        if target in imports(source):
            return {"consumer_result_id": peer["id"], "imported_result_id": anchor_id}
        return None

    def proof_bundle(result: dict[str, Any]) -> dict[str, Any]:
        argument = arguments[result["argument_id"]]
        return {
            "result_id": result["id"], "argument_id": argument["id"],
            "theorem": result.get("theorem"), "recorded_status": result.get("status"),
            "premise_statement_ids": list(argument["premise_statement_ids"]),
            "conclusion_statement_id": argument["conclusion_statement_id"],
        }

    root_facing = set(frontier.get("reaching_root_statements", []))
    closed = set(frontier.get("closed_statements", []))
    candidates = []
    excluded = {"cross_profile": 0, "different_witness": 0, "no_direct_reuse": 0, "no_remaining_question": 0}
    linked_attempts = 0
    anchor_conclusion = arguments[anchor["argument_id"]]["conclusion_statement_id"]
    for attempt in sorted(data["attempts"], key=lambda entry: entry["id"]):
        evidence = attempt.get("evidence", [])
        if anchor_id not in evidence:
            continue
        linked_attempts += 1
        if not attempt.get("blocker"):
            excluded["no_remaining_question"] += 1
            continue

        # An attempt may cite an unrelated result as contextual evidence.
        # Require both *conclusions* to be its explicit focus before suggesting
        # a bridge; a mere evidence-list or import overlap is insufficient.
        focus_set = set(attempt.get("statement_ids", []))
        if anchor_conclusion not in focus_set:
            excluded["cross_profile"] += 1
            continue
        eligible = []
        edges = []
        for other_id in sorted(set(evidence)):
            if other_id not in results or other_id == anchor_id:
                continue
            other = results[other_id]
            if arguments[other["argument_id"]]["conclusion_statement_id"] not in focus_set:
                excluded["cross_profile"] += 1
                continue
            if not in_profile(other):
                excluded["cross_profile"] += 1
                continue
            if not scope_compatible(anchor, other):
                excluded["different_witness"] += 1
                continue
            edge = direct_edge(other)
            if edge is None or other["argument_id"] == anchor["argument_id"]:
                excluded["no_direct_reuse"] += 1
                continue
            eligible.append(other)
            edges.append(edge)

        if not eligible:
            continue
        focus = sorted(set(attempt.get("statement_ids", [])) & statements.keys())
        open_focus = [sid for sid in focus if sid not in closed]
        on_root = [sid for sid in open_focus if sid in root_facing]
        # Names are navigation hints only; they cannot certify negative controls.
        controls = sorted({rid for rid in evidence if rid in results and
                           re.search(r"(?:CONTROL|OMISSION|COUNTERMODEL)", rid) and
                           in_profile(results[rid]) and scope_compatible(anchor, results[rid])})
        # Score ranks a *bounded test opportunity*, not philosophical truth.
        score = (5 * min(len(on_root), 3) + 4 * (attempt.get("outcome") == "blocked") +
                 2 * min(len(edges), 3) + 2 * bool(controls) + bool(open_focus))
        candidates.append({
            "attempt_id": attempt["id"], "attempt_outcome": attempt.get("outcome"),
            "recorded_blocker": attempt["blocker"],
            "focus_statement_ids": focus, "open_focus_statement_ids": open_focus,
            "open_root_facing_statement_ids": on_root,
            "exact_import_edges": sorted(edges, key=lambda e: (e["consumer_result_id"], e["imported_result_id"])),
            "full_argument_bundles": [proof_bundle(result) for result in
                                      sorted([anchor, *eligible], key=lambda item: item["id"])],
            "control_hint_result_ids": controls,
            "negative_test": "Attempt a SAME-PROFILE counterinterpretation satisfying each complete premise bundle while denying the proposed bridge. Compare a positive interpretation, the strongest rival, and an omission control. An absent proof is not a countermodel.",
            "priority_score": score,
            "priority_reasons": {"root_facing_open": len(on_root), "blocked_attempt": attempt.get("outcome") == "blocked",
                                 "direct_reuse_edges": len(edges), "named_control_hints": len(controls)},
            "qualification": "Registered evidence and an exact Solution import only. Inspect theorem types, common interpretation and negative controls; no new entailment or philosophical closure follows.",
        })
    candidates.sort(key=lambda entry: (-entry["priority_score"], entry["attempt_id"]))
    return {
        "mode": "registered-evidence discovery; NOT a proof or refutation",
        "anchor_result_id": anchor_id, "requested_profile_module": profile_module,
        "profile_boundary": "All displayed Solution modules import this exact Lean module. Shared imports do not establish the same semantic instantiation or witness; inspect complete types before combining them. Explicit profile/witness metadata mismatches are excluded.",
        "summary": {"linked_attempts": linked_attempts, "eligible_experiments": len(candidates),
                    "excluded_peer_reasons": excluded},
        "experiments": candidates[:limit],
        "truncated": max(0, len(candidates) - limit),
        "absence_warning": "The absence of a candidate or recorded proof is NOT a refutation. Do not infer a worldview result from this discovery report.",
    }


def format_experiments(report: dict[str, Any]) -> str:
    lines = [f"Cross-argument experiments from {report['anchor_result_id']}",
             f"Selected profile module: {report['requested_profile_module']}",
             "Discovery only; direct imports are not proof of common instantiation."]
    for i, candidate in enumerate(report["experiments"], 1):
        lines.extend([f"\n{i}. {candidate['attempt_id']} [priority {candidate['priority_score']}; {candidate['attempt_outcome']}]",
                      f"   Open question: {candidate['recorded_blocker'][:400]}" +
                      ("... (full in --json)" if len(candidate["recorded_blocker"]) > 400 else ""),
                      "   Exact Solution imports: " + ", ".join(
                          f"{edge['consumer_result_id']} imports {edge['imported_result_id']}"
                          for edge in candidate["exact_import_edges"]),
                      "   Open focus statements: " + (", ".join(candidate["open_focus_statement_ids"]) or "none"),
                      "   Control hints (read the theorems): " +
                      (", ".join(candidate["control_hint_result_ids"]) or "none recorded by name"),
                      "   Use --json for the complete AND-premise bundles, priority and negative-test protocol."])
    if not report["experiments"]:
        lines.append("No eligible same-module direct-import experiments found. This is NOT a refutation.")
    if report["truncated"]:
        lines.append(f"{report['truncated']} additional candidates; increase --limit (maximum 20).")
    return "\n".join(lines)
