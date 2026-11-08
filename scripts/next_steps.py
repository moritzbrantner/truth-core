"""The next-work projection produced inside the authoritative frontier computation.

This module never decides closure or recomputes proof validity. The frontier
supplies current established/refuted sets and a probe of its own fixpoint for
counterfactual costs. CLI and explorer consume the resulting JSON verbatim.
"""
from __future__ import annotations

from itertools import combinations
from typing import Any, Callable

SETTLEMENT_RULES = {
    "floor": "Accept an explicit starting point. Each new floor item requires an owner decision; a proposed item settles nothing.",
    "derive": "Use a verified argument and establish every premise it needs. A conditional proof alone does not settle its conclusion.",
    "defend": "Refute every recorded rival using verified arguments whose premises are all established. An unrecorded rival may still matter philosophically.",
}


def next_steps_report(report: dict, statements: list[dict], arguments: list[dict],
                      results: list[dict], relations: list[dict],
                      probe: Callable[[str], dict]) -> dict:
    """Navigation and ranking, with all truth/closure decisions supplied by frontier."""
    statements = sorted(statements, key=lambda item: item["id"])
    arguments = sorted(arguments, key=lambda item: item["id"])
    results = sorted(results, key=lambda item: item["id"])
    relations = sorted(relations, key=lambda item: item["id"])
    statement_by_id = {s["id"]: s for s in statements}
    argument_by_id = {a["id"]: a for a in arguments}
    result_ids: dict[str, list[str]] = {}
    for result in results:
        result_ids.setdefault(result["argument_id"], []).append(result["id"])
    established = set(report["established_statements"])
    refuted = set(report["refuted_statements"])
    routes = report["routes"]["routes"]
    cheapest = next((r for r in routes if r["cheapest"]), None)
    leaves = sorted({sid for route in routes for sid in route["open_premise_statement_ids"]})
    alternatives: dict[str, list[str]] = {}
    for relation in relations:
        if relation.get("predicate") == "alternative_to":
            alternatives.setdefault(relation["object_id"], []).append(relation["subject_id"])
    refutations: dict[str, list[dict]] = {}
    for refutation in report["refutations"]:
        refutations.setdefault(refutation["statement_id"], []).append(refutation)

    def statement(sid: str) -> dict:
        record = statement_by_id.get(sid, {})
        return {"statement_id": sid, "paraphrase": record.get("paraphrase", sid),
                "established": sid in established,
                "status": report["statement_statuses"].get(sid, "open"),
                "depth": report["statement_depths"].get(sid),
                "lean_declaration": record.get("lean_declaration"),
                "definition_ids": record.get("definition_ids", [])}

    def derivation(argument: dict) -> dict:
        premises = argument["premise_statement_ids"]
        return {"argument_id": argument["id"], "meaning": argument.get("meaning", ""),
                "conclusion_statement_id": argument["conclusion_statement_id"],
                "premise_statement_ids": premises,
                "missing_statement_ids": [sid for sid in premises if sid not in established],
                "result_ids": result_ids.get(argument["id"], []),
                "verified": bool(result_ids.get(argument["id"])),
                "transcription": bool(result_ids.get(argument["id"])) and all(rid in report["transcription_results"]
                                     for rid in result_ids.get(argument["id"], []))}

    def rival(sid: str) -> dict:
        return {**statement(sid), "refuted": sid in refuted,
                "refutations": refutations.get(sid, []),
                "consequences": [derivation(a) for a in arguments
                                 if sid in a["premise_statement_ids"]]}

    leaf_rows = []
    for sid in leaves:
        # Probe the same least fixpoint as the actual frontier, including
        # consequences and newly counted refutations, then rerun its route cost.
        hypothetical = {r["argument_id"]: r for r in probe(sid)["routes"]}
        impacts = [{"argument_id": route["argument_id"], "before": route["cost"],
                    "after": hypothetical[route["argument_id"]]["cost"],
                    "drop": route["cost"] - hypothetical[route["argument_id"]]["cost"]}
                   for route in routes if route["verified"]
                   and route["cost"] != hypothetical[route["argument_id"]]["cost"]]
        recorded_rivals = [rival(rid) for rid in sorted(set(alternatives.get(sid, [])))]
        derivations = [derivation(a) for a in arguments if a["conclusion_statement_id"] == sid]
        leaf_rows.append({**statement(sid),
                          "route_depths": {r["argument_id"]: r["open_premise_depths"][sid]
                                           for r in routes if sid in r["open_premise_statement_ids"]},
                          "on_cheapest_route": bool(cheapest and sid in cheapest["open_premise_statement_ids"]),
                          "rivals": recorded_rivals, "derivations": derivations,
                          "floor": {"owner_decision_required": True,
                                    "marking": next((f for f in report["floor"] if f["statement_id"] == sid), None)},
                          "definition_decisions": statement_by_id.get(sid, {}).get("settlement_actions", []),
                          "impact": {"routes_improved": sum(x["drop"] > 0 for x in impacts),
                                     "total_cost_drop": sum(x["drop"] for x in impacts), "routes": impacts},
                          "defense": {"recorded_rival_count": len(recorded_rivals),
                                      "undefeated_statement_ids": [r["statement_id"] for r in recorded_rivals if not r["refuted"]],
                                      "coverage": "recorded rivals only; not a certified exhaustive partition"}})
    leaf_rows.sort(key=lambda x: (-x["impact"]["routes_improved"], -x["impact"]["total_cost_drop"], x["statement_id"]))

    # Shared leaves are shared failure modes, not evidence of incompatibility.
    # Enumerate every leaf failure separately: a rival can be relevant without
    # being the logical negation of that leaf. Only a future explicit certificate
    # can turn these navigation candidates into a joint settlement.
    def failures(route: dict) -> list[dict]:
        return [{"statement_id": sid, "failure": f"not ({sid})",
                 "recorded_rivals": [rival(rid) for rid in sorted(set(alternatives.get(sid, [])))],
                 "negation_consequence_coverage": "unresolved: no certificate covering this failure mode registered"}
                for sid in route["open_premise_statement_ids"]]

    verified_routes = [r for r in routes if r["verified"]]
    pairs = []
    for left, right in combinations(verified_routes, 2):
        overlap = sorted(set(left["open_premise_statement_ids"]) & set(right["open_premise_statement_ids"]))
        pairs.append({"left_argument_id": left["argument_id"], "right_argument_id": right["argument_id"],
                      "shared_statement_ids": overlap, "overlap_count": len(overlap),
                      "left_failure_statement_ids": left["open_premise_statement_ids"],
                      "right_failure_statement_ids": right["open_premise_statement_ids"],
                      "certified": False,
                      "remaining": ["Cover every failure mode of each route by a consequence theorem.",
                                    "Establish incompatibility of the two consequences, with all its premises settled.",
                                    "Compose both route implications with the joint-failure certificate." ]})
    pairs.sort(key=lambda pair: (pair["overlap_count"], pair["left_argument_id"], pair["right_argument_id"]))
    # A disjunction of fixed conjunctive bundles still entails each conjunct
    # shared by every bundle. This is only a property of frontier's *reported*
    # sufficient bundles, not a search over all possible root derivations.
    joint_summary = {
        "verified_route_count": len(verified_routes),
        "pair_count": len(pairs),
        "minimum_pair_overlap": pairs[0]["overlap_count"] if pairs else None,
        "shared_by_all_reported_routes": sorted(set.intersection(*(
            set(route["open_premise_statement_ids"]) for route in verified_routes
        ))) if len(verified_routes) > 1 else [],
        "scope": "Intersection of the reported verified root bundles only; not an exhaustive set of possible routes or a proof of necessary premises.",
    }

    partitions = []
    for result in results:
        annotation = result.get("case_split")
        if not annotation:
            continue
        argument = argument_by_id[result["argument_id"]]
        cells = []
        for cell in annotation["cases"]:
            case_sid = cell.get("statement_id")
            cells.append({**cell, "refuted": case_sid in refuted if case_sid else False,
                          "refutations": refutations.get(case_sid, []) if case_sid else [],
                          "refutation_scope": "counted refutations of the registered case statement" if case_sid else
                                              "no independent case statement; no counted refutation registered"})
        partitions.append({"result_id": result["id"], "theorem": result.get("theorem"),
                           "target_statement_id": annotation["target_statement_id"],
                           "target_established": annotation["target_statement_id"] in established,
                           "coverage_statement_id": argument["conclusion_statement_id"],
                           "missing_background_statement_ids": [sid for sid in argument["premise_statement_ids"] if sid not in established],
                           "cases": cells,
                           "survival_result_id": annotation.get("survival_result_id"),
                           "note": annotation.get("note", "")})
    reaching_root = set(report["reaching_root_statements"])
    graph_arguments = [derivation(a) for a in arguments if a["conclusion_statement_id"] in reaching_root]
    graph_ids = set(report["reaching_root_statements"])
    graph_ids.update(sid for a in graph_arguments for sid in a["premise_statement_ids"])
    floor = [{**entry, **statement(entry["statement_id"]),
              "rivals": [rival(rid) for rid in sorted(set(alternatives.get(entry["statement_id"], [])))],
              "dependents": report["premise_dependents"].get(entry["statement_id"], {"arguments": [], "statements": []})}
             for entry in report["floor"]]
    options = report["support_options"]
    progress = {
        "root_reaching_established_count": len(established & reaching_root),
        "unestablished_premise_count": options["unestablished_premise_count"],
        "with_verified_alternative_count": options["with_verified_alternative_count"],
        "verified_alternative_bundle_count": options["verified_alternative_bundle_count"],
    }
    return {"root": statement(report["root"]) if report["root"] else None,
            "root_known": report["root_known"], "progress": progress, "support_options": options, "settlement_rules": SETTLEMENT_RULES,
            "impact_scope": "Counterfactual: establish this leaf alone, propagate the frontier's existing rules, and recompute all verified route costs. No actual approval, proof, or settlement is added.",
            "routes": routes, "cheapest_argument_id": report["routes"]["cheapest_argument_id"],
            "leaves": leaf_rows, "joint_settlements": pairs,
            "joint_settlement_summary": joint_summary, "partitions": partitions,
            "joint_settlement_schema_result_ids": [r["id"] for r in results if r.get("joint_settlement_schema") is True],
            "failure_modes": {mode["statement_id"]: mode for route in routes for mode in failures(route)},
            "floor_register": floor,
            "owner_decisions": [{"statement_id": leaf["statement_id"], "paraphrase": leaf["paraphrase"],
                                 "impact": leaf["impact"], "actions": leaf["definition_decisions"]}
                                for leaf in leaf_rows if leaf["definition_decisions"]],
            "dag": {"statements": [statement(sid) for sid in sorted(graph_ids)], "arguments": graph_arguments}}


def format_next_steps(report: dict) -> str:
    root = report.get("root")
    lines = [f"Next steps for {root['statement_id'] if root else 'no root'}"]
    progress = report["progress"]
    lines.append(
        f"Foundational progress: {progress['root_reaching_established_count']} established root-reaching statements; "
        f"{progress['with_verified_alternative_count']} of {progress['unestablished_premise_count']} "
        "unestablished premises with verified support alternatives; "
        f"{progress['verified_alternative_bundle_count']} distinct conditional bundles"
    )
    lines.append("Inspectable premise support options (conditional; not independence certificates):")
    for item in report["support_options"]["items"]:
        lines.append(f"  {item['statement_id']}: " + ("direct assumption available" if item["direct_assumption_available"] else "established in corpus"))
        for bundle in item["verified_alternative_bundles"]:
            lines.append("    premises: " + (", ".join(bundle["premise_statement_ids"]) or "none"))
            lines.append("    arguments: " + ", ".join(bundle["argument_ids"]))
            lines.append("    verified results: " + ", ".join(bundle["result_ids"]))
    lines.extend(f"{kind}: {text}" for kind, text in report["settlement_rules"].items())
    lines.append("Expanded routes (cost diagnostic; joint settlement unresolved without complete failure-mode coverage):")
    lines.extend(f"  {route['cost']:>3} {route['argument_id']}" for route in report["routes"])
    lines.append("Lowest-expanded-cost route leaves, ranked by counterfactual settlement impact (diagnostic):")
    for leaf in report["leaves"]:
        if not leaf["on_cheapest_route"]:
            continue
        lines.append(f"  {leaf['statement_id']} [{leaf['depth'] or 'proved from open premises'}]: "
                     f"{leaf['impact']['routes_improved']} routes improve; total cost drop {leaf['impact']['total_cost_drop']}")
        lines.append("    floor: owner decision required")
        for proof in leaf["derivations"]:
            lines.append(f"    derive via {proof['argument_id']}: missing {', '.join(proof['missing_statement_ids']) or 'none'}"
                         + (" (no verified result)" if not proof["verified"] else ""))
        lines.append("    defend: undefeated recorded rivals " + ", ".join(leaf["defense"]["undefeated_statement_ids"]))
    lines.append("Recorded owner decisions:")
    for decision in report["owner_decisions"]:
        for action in decision["actions"]:
            lines.append(f"  {decision['statement_id']}: {action['kind']} / {action['status']}: {action['description']}")
    lines.append("Partition opportunities:")
    for partition in report["partitions"]:
        lines.append(f"  {partition['result_id']}: target {partition['target_statement_id']}; missing background {', '.join(partition['missing_background_statement_ids']) or 'none'}")
        for cell in partition["cases"]:
            lines.append(f"    {cell['label']}: {'refuted' if cell['refuted'] else 'undefeated'} ({cell['lean_declaration']})")
    lines.append(f"Joint settlement: {len(report['joint_settlements'])} unresolved route pairs; see JSON for all failure modes.")
    joint = report["joint_settlement_summary"]
    lines.append(f"Shared by all {joint['verified_route_count']} reported verified routes: "
                 f"{len(joint['shared_by_all_reported_routes'])} open obligations (not exhaustive route necessity).")
    lines.extend(f"  {sid}" for sid in joint["shared_by_all_reported_routes"])
    lines.append(report["impact_scope"])
    return "\n".join(lines)


def validate_settlement_actions(statement: dict) -> None:
    """Optional owner-navigation hints never participate in closure."""
    actions = statement.get("settlement_actions", [])
    if not isinstance(actions, list):
        raise ValueError("settlement_actions must be a list")
    for action in actions:
        if not isinstance(action, dict) or action.get("kind") not in {"floor", "definition"}:
            raise ValueError("settlement action must have kind floor or definition")
        if action.get("status") not in {"needs-owner-decision", "approved"} or not isinstance(action.get("description"), str) or not action["description"]:
            raise ValueError("settlement action needs a description and status needs-owner-decision or approved")
        if action.get("status") == "approved" and not str(action.get("decision", "")).startswith("https://github.com/moritzbrantner/truth-core/"):
            raise ValueError("approved settlement action needs a repository owner decision URL")


def validate_case_split(result: dict, statement_ids: set[str], result_ids: set[str]) -> None:
    """Validate navigation references; proof/type fidelity remains a self-sweep duty."""
    if "joint_settlement_schema" in result and type(result["joint_settlement_schema"]) is not bool:
        raise ValueError("joint_settlement_schema must be boolean navigation metadata")
    split = result.get("case_split")
    if split is None:
        return
    if not isinstance(split, dict) or split.get("target_statement_id") not in statement_ids:
        raise ValueError("case_split needs a known target_statement_id")
    if split.get("survival_result_id") is not None and split["survival_result_id"] not in result_ids:
        raise ValueError("case_split survival_result_id must name a known result")
    cases = split.get("cases")
    if not isinstance(cases, list) or not cases:
        raise ValueError("case_split needs nonempty cases")
    declarations = []
    for case in cases:
        if not isinstance(case, dict) or not isinstance(case.get("label"), str) or not case["label"]:
            raise ValueError("case_split case needs a label")
        declaration = case.get("lean_declaration")
        if not isinstance(declaration, str) or not declaration.startswith("TruthCore."):
            raise ValueError("case_split case needs a TruthCore lean_declaration")
        declarations.append(declaration)
        if case.get("statement_id") is not None and case["statement_id"] not in statement_ids:
            raise ValueError("case_split case statement_id must name a known statement")
    if len(set(declarations)) != len(declarations):
        raise ValueError("case_split case declarations must be distinct")
