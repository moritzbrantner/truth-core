"""Emergent positions and the territory matrix (#512).

Nothing here is hand-authored: positions are computed from records the corpus
already has, and the tool writes no corpus record. Which records feed which
relation:

* **Atoms** are statement IDs. The bounded universe is built in one round:
  the open root-path premises (`frontier`, `path_to_root` set), their recorded
  rivals (`alternative_to`, either direction), the atoms of every certified
  core whose statements are derivable from those (see below), every statement
  evaluated by a registered model (`corpus/models/`) that evaluates one of
  them, and every commitment of a consistency result (an argument with
  `commitment_statement_ids`, i.e. a per-question theory bundle opened to its
  flat conjuncts) that commits to one of them.
* **Incompatibility (certified cores):** (a) a registered, non-transcription
  result whose conclusion statement is `TruthCore.Logic.ConfigurationFalse`:
  its exact premise set; (b) a `refutes` relation whose argument has a
  registered, non-transcription result: the argument's premises plus the
  refuted statement (open premises included: a core certifies that the set is
  inconsistent, not that any member is false).
* **Entailment:** every other registered non-transcription result that is not
  a consistency result: its argument's premises entail its conclusion.
* **Compatibility (witnesses):** a registered model satisfies the set of
  statements it evaluates `satisfies` (one model is read as one
  interpretation, as `corpus.py models --premise` does); a registered
  non-transcription consistency result witnesses its commitment set.
* **Attestation:** claims (`claim.statement_id`) grouped by their source's
  `author`. `supports` relations do not attest.

Registered means what `frontier` treats as verified; CI rebuilds and checks
every result and model. Absence of a core is never consistency and absence of
a witness is never inconsistency: positions without a witness are reported as
`not_known_inconsistent`.

Conflicts are minimal sets of universe atoms whose verified-entailment closure
contains a certified core (supports via `configurations.implication_closure`).
Atoms linked by conflicts form components (independent questions); a local
position is a maximal conflict-free subset of one component (the complement of
a minimal hitting set of its conflicts), closed under entailment by
maximality. Global positions, the maximal conflict-free subsets of the whole
universe, are exactly the products of local positions, so they are counted
exactly and enumerated only up to a bound. IDs hash the sorted atom set.
"""
from __future__ import annotations

import hashlib
from itertools import product
from typing import Any

from configurations import implication_closure

FALSE_DECLARATION = "TruthCore.Logic.ConfigurationFalse"
SCOPE = (
    "Computed from registered cores, entailments, models, consistency results and claims only; "
    "no position is named or hand-authored and no corpus record is written. Positions are maximal "
    "relative to the reported bounded atom universe and certified cores only: absence of a core is not "
    "consistency, absence of a witness is not inconsistency. common_ground entries are candidates; "
    "marking one still needs #501/#378 evidence."
)


def position_id(atoms: Any) -> str:
    digest = hashlib.sha256("\n".join(sorted(atoms)).encode("utf-8")).hexdigest()
    return "POS-" + digest[:12].upper()


def certified_cores(arguments, results, relations, statements, transcription_results):
    """Certified incompatible statement sets, with their evidence."""
    false_ids = {sid for sid, record in statements.items() if record.get("lean_declaration") == FALSE_DECLARATION}
    usable = {}
    for rid in sorted(results):
        result = results[rid]
        if rid in transcription_results or result.get("argument_id") not in arguments:
            continue
        usable.setdefault(result["argument_id"], rid)
    cores = []
    for argument_id, rid in sorted(usable.items()):
        argument = arguments[argument_id]
        if argument["conclusion_statement_id"] in false_ids:
            cores.append({"statement_ids": sorted(set(argument["premise_statement_ids"])), "kind": "derives_false",
                          "result_id": rid, "argument_id": argument_id, "relation_id": None})
    for relation in sorted(relations, key=lambda item: item["id"]):
        if relation.get("predicate") != "refutes" or relation["subject_id"] not in usable:
            continue
        argument = arguments[relation["subject_id"]]
        cores.append({"statement_ids": sorted(set(argument["premise_statement_ids"]) | {relation["object_id"]}),
                      "kind": "refutes", "result_id": usable[relation["subject_id"]],
                      "argument_id": argument["id"], "relation_id": relation["id"]})
    return cores


def entailment_rules(arguments, results, statements, transcription_results):
    """One registered non-transcription result per argument; no cores, no consistency results."""
    false_ids = {sid for sid, record in statements.items() if record.get("lean_declaration") == FALSE_DECLARATION}
    chosen = {}
    for rid in sorted(results):
        result = results[rid]
        argument = arguments.get(result.get("argument_id"))
        if rid in transcription_results or argument is None:
            continue
        if argument.get("commitment_statement_ids") or argument["conclusion_statement_id"] in false_ids:
            continue
        chosen.setdefault(argument["id"], rid)
    return sorted(chosen.values())


def witnesses(models, arguments, results, transcription_results):
    """(kind, id, satisfied statements, violated statements) for every certified witness."""
    found = []
    for model in sorted(models, key=lambda item: item["id"]):
        values = {item["statement_id"]: item["value"] for item in model["evaluations"]}
        found.append(("model", model["id"], frozenset(s for s, v in values.items() if v == "satisfies"),
                      frozenset(s for s, v in values.items() if v == "violates")))
    seen = set()
    for rid in sorted(results):
        argument = arguments.get(results[rid].get("argument_id"))
        if rid in transcription_results or argument is None or not argument.get("commitment_statement_ids") or argument["id"] in seen:
            continue
        seen.add(argument["id"])
        found.append(("consistency_result", rid, frozenset(argument["commitment_statement_ids"]), frozenset()))
    return found


def minimal_sets(sets):
    unique = sorted({frozenset(item) for item in sets}, key=lambda item: (len(item), sorted(item)))
    kept = []
    for item in unique:
        if not any(other <= item for other in kept):
            kept.append(item)
    return kept


def minimal_hitting_sets(conflicts, limit):
    """Berge's algorithm, deterministic; returns (sets, truncated).

    On truncation no sets are returned: a partial antichain need not hit every
    conflict, so its complements could contain a certified conflict."""
    hitting = [frozenset()]
    for conflict in sorted(conflicts, key=lambda item: (len(item), sorted(item))):
        grown = []
        for current in hitting:
            if current & conflict:
                grown.append(current)
            else:
                grown.extend(current | {atom} for atom in sorted(conflict))
        hitting = minimal_sets(grown)
        if len(hitting) > limit:
            return [], True
    return hitting, False


def territory_report(*, statements, arguments, results, relations, claims, sources, models, transcription_results,
                     seeds, routes, max_atoms=512, closure_limit=20000, core_combination_limit=4096,
                     hitting_set_limit=1024, global_position_limit=64):
    """`seeds`: [{statement_id, transitive_dependent_arguments}]; `routes`: root routes from frontier."""
    seed_ids = sorted({item["statement_id"] for item in seeds})
    alternatives = {}
    for relation in relations:
        if relation.get("predicate") == "alternative_to":
            alternatives.setdefault(relation["object_id"], set()).add(relation["subject_id"])
            alternatives.setdefault(relation["subject_id"], set()).add(relation["object_id"])
    rivals = {seed: sorted(alternatives.get(seed, ())) for seed in seed_ids}
    rival_ids = sorted({rival for values in rivals.values() for rival in values} - set(seed_ids))
    cores = certified_cores(arguments, results, relations, statements, transcription_results)
    rule_ids = entailment_rules(arguments, results, statements, transcription_results)
    case = {"implication_result_ids": rule_ids}
    certified_witnesses = witnesses(models, arguments, results, transcription_results)

    # Universe: one expansion round from seeds and rivals.
    base = set(seed_ids) | set(rival_ids)
    reachable = {item["statement_id"] for item in implication_closure(base, case, results, arguments, limit=closure_limit, include_assumptions=True)["items"]}
    added_cores = sorted({sid for core in cores if set(core["statement_ids"]) & reachable for sid in core["statement_ids"]} - base)
    added_witness = sorted({sid for _, _, sat, vio in certified_witnesses if (sat | vio) & base for sid in sat | vio} - base - set(added_cores))
    ordered = seed_ids + rival_ids + added_cores + added_witness
    universe_truncated = len(ordered) > max_atoms
    universe = ordered[:max_atoms]
    atoms = set(universe)

    closure = implication_closure(atoms, case, results, arguments, limit=closure_limit, include_assumptions=True)
    supports = {item["statement_id"]: [frozenset(option["statement_ids"]) for option in item["sufficient_subsets"]] for item in closure["items"]}
    support_chains = {item["statement_id"]: item["sufficient_subsets"] for item in closure["items"]}
    unconditional = sorted(sid for sid, options in supports.items() if frozenset() in options and sid not in atoms)

    conflict_evidence = {}
    combinations_checked = 0
    core_truncated = False
    for core in cores:
        if any(sid not in supports for sid in core["statement_ids"]):
            continue
        for chosen in product(*(support_chains[sid] for sid in core["statement_ids"])):
            combinations_checked += 1
            if combinations_checked > core_combination_limit:
                core_truncated = True
                break
            subset = frozenset(sid for option in chosen for sid in option["statement_ids"])
            chain = list(dict.fromkeys([rid for option in chosen for rid in option["result_ids"]] + [core["result_id"]]))
            conflict_evidence.setdefault(subset, {"statement_ids": sorted(subset), "core_statement_ids": core["statement_ids"],
                                                  "kind": core["kind"], "relation_id": core["relation_id"],
                                                  "result_ids": chain})
        if core_truncated:
            break
    conflicts = minimal_sets(conflict_evidence)
    defects = []
    if frozenset() in conflicts:
        defects.append({"kind": "inconsistent_without_atoms", "conflict": conflict_evidence[frozenset()]})
        conflicts = [conflict for conflict in conflicts if conflict]
    for kind, wid, satisfied, _ in certified_witnesses:
        for conflict in conflicts:
            if conflict <= satisfied:
                defects.append({"kind": "witness_satisfies_conflict", "witness": {"kind": kind, "id": wid},
                                "conflict": conflict_evidence[conflict]})

    # Components: atoms linked by a shared minimal conflict.
    parent = {atom: atom for atom in universe}

    def find(atom):
        while parent[atom] != atom:
            parent[atom] = parent[parent[atom]]
            atom = parent[atom]
        return atom
    for conflict in conflicts:
        first, *rest = sorted(conflict)
        for atom in rest:
            a, b = find(first), find(atom)
            if a != b:
                parent[max(a, b)] = min(a, b)
    groups = {}
    for atom in universe:
        groups.setdefault(find(atom), []).append(atom)

    author_of = {sid: (record.get("author") or "unknown") for sid, record in sources.items()}
    claims_by_statement = {}
    for claim in sorted(claims, key=lambda item: item["id"]):
        claims_by_statement.setdefault(claim["statement_id"], []).append(claim)

    def attestation(position_atoms):
        by_author = {}
        for sid in sorted(position_atoms):
            for claim in claims_by_statement.get(sid, []):
                entry = by_author.setdefault(author_of.get(claim["source_id"], "unknown"), {"source_ids": set(), "claim_ids": [], "statement_ids": set()})
                entry["source_ids"].add(claim["source_id"])
                entry["claim_ids"].append(claim["id"])
                entry["statement_ids"].add(sid)
        rows = [{"author": author, "source_ids": sorted(entry["source_ids"]), "claim_ids": sorted(entry["claim_ids"]),
                 "statement_ids": sorted(entry["statement_ids"]), "covers_all": entry["statement_ids"] == set(position_atoms)}
                for author, entry in sorted(by_author.items())]
        return {"attested_by": [row["author"] for row in rows if row["covers_all"]], "stating_authors": rows}

    def witnessing(position_atoms):
        return [{"kind": kind, "id": wid} for kind, wid, satisfied, _ in certified_witnesses if set(position_atoms) <= satisfied]

    def entailed(position_atoms):
        chosen = frozenset(position_atoms)
        return sorted(sid for sid, options in supports.items()
                      if sid not in chosen and any(option and option <= chosen for option in options))

    components = []
    local_positions = {}
    position_component = {}
    hitting_truncated = False
    for index, (_, members) in enumerate(sorted(groups.items(), key=lambda item: sorted(item[1]))):
        members = sorted(members)
        member_set = set(members)
        local_conflicts = [conflict for conflict in conflicts if conflict <= member_set]
        hitting, truncated = minimal_hitting_sets(local_conflicts, hitting_set_limit)
        hitting_truncated |= truncated
        ids = []
        for removed in hitting:
            position_atoms = sorted(member_set - removed)
            pid = position_id(position_atoms)
            found = witnessing(position_atoms)
            local_positions[pid] = {"id": pid, "atom_ids": position_atoms, "excluded_atom_ids": sorted(removed),
                                    "entailed_statement_ids": entailed(position_atoms),
                                    "status": "witnessed" if found else "not_known_inconsistent",
                                    "witnesses": found, **attestation(position_atoms)}
            position_component[pid] = index
            ids.append(pid)
        ids.sort()
        in_some = {atom for pid in ids for atom in local_positions[pid]["atom_ids"]}
        components.append({"index": index, "atom_ids": members, "position_ids": ids,
                           "conflicts": [conflict_evidence[conflict] for conflict in local_conflicts],
                           "eliminated_atom_ids": [] if truncated else sorted(member_set - in_some),
                           "hitting_sets_truncated": truncated})
    eliminated_atoms = {atom for component in components for atom in component["eliminated_atom_ids"]}

    # A truncated component has withheld positions, so the global count is unknown.
    global_count = None if hitting_truncated else 1
    for component in components if not hitting_truncated else []:
        global_count *= len(component["position_ids"])
    global_positions = []
    for chosen in product(*(component["position_ids"] for component in components)) if not hitting_truncated else []:
        if len(global_positions) >= global_position_limit:
            break
        position_atoms = sorted(atom for pid in chosen for atom in local_positions[pid]["atom_ids"])
        found = witnessing(position_atoms)
        global_positions.append({"id": position_id(position_atoms), "local_position_ids": sorted(chosen),
                                 "atom_count": len(position_atoms),
                                 "status": "witnessed" if found else "not_known_inconsistent", "witnesses": found,
                                 "attested_by": attestation(position_atoms)["attested_by"]})

    route_entries = [route for route in routes if route.get("verified")]
    dependents = {item["statement_id"]: len(item.get("transitive_dependent_arguments", [])) for item in seeds}
    component_of = {atom: component["index"] for component in components for atom in component["atom_ids"]}

    def rival_class(seed, rival):
        pair = {seed, rival}
        if any(conflict <= pair and rival in conflict for conflict in conflicts):
            return "certified_incompatible"
        return "uncertified"

    rows = []
    for seed in seed_ids:
        if seed not in component_of:
            rows.append({"statement_id": seed, "classification": "outside_bound", "values": {}, "in_position_ids": [],
                         "out_position_ids": [], "routes": 0, "cheapest_route_cost": None,
                         "transitive_dependents": dependents.get(seed, 0), "rivals": [], "stating_authors": []})
            continue
        component = components[component_of[seed]]
        values = {}
        for pid in sorted(local_positions):
            if position_component[pid] != component["index"]:
                values[pid] = "undetermined"
            else:
                values[pid] = "in" if seed in local_positions[pid]["atom_ids"] else "out"
        in_ids = [pid for pid, value in values.items() if value == "in"]
        out_ids = [pid for pid, value in values.items() if value == "out"]
        witnessed_in = [pid for pid in in_ids if local_positions[pid]["status"] == "witnessed"]
        recorded = [{"statement_id": rival, "class": rival_class(seed, rival)} for rival in rivals[seed]]
        eliminated = eliminated_atoms
        if component["hitting_sets_truncated"]:
            classification = "enumeration_truncated"
        elif not in_ids:
            classification = "eliminated"
        elif out_ids:
            classification = "split"
        elif recorded and all(item["statement_id"] in eliminated for item in recorded):
            classification = "rivals_eliminated"
        elif recorded:
            classification = "contested_uncertified"
        elif witnessed_in:
            classification = "common_ground_candidate"
        else:
            classification = "unwitnessed"
        on_routes = [route for route in route_entries if seed in route["open_premise_statement_ids"]]
        rows.append({"statement_id": seed, "classification": classification, "values": values,
                     "in_position_ids": in_ids, "out_position_ids": out_ids,
                     "witnessed_in_position_ids": witnessed_in,
                     "excluding_conflicts": [conflict_evidence[conflict] for conflict in conflicts if seed in conflict],
                     "routes": len(on_routes),
                     "cheapest_route_cost": min((route["cost"] for route in on_routes), default=None),
                     "transitive_dependents": dependents.get(seed, 0), "rivals": recorded,
                     "stating_authors": [row["author"] for row in attestation([seed])["stating_authors"]]})
    splits = sorted((row for row in rows if row["classification"] == "split"),
                    key=lambda row: (-row["routes"], -row["transitive_dependents"], row["statement_id"]))
    summary_counts = {}
    for row in rows:
        summary_counts[row["classification"]] = summary_counts.get(row["classification"], 0) + 1
    return {
        "scope": SCOPE,
        "bounds": {"universe": "one expansion round: root-path open premises, their recorded rivals, atoms of "
                               "certified cores derivable from those, statements of models/consistency results "
                               "that evaluate or commit to one of them",
                   "max_atoms": max_atoms, "atom_count": len(universe), "universe_truncated": universe_truncated,
                   "closure_limit": closure_limit, "closure_truncated": closure["truncated"],
                   "core_combination_limit": core_combination_limit, "core_combinations_checked": min(combinations_checked, core_combination_limit),
                   "core_combinations_truncated": core_truncated,
                   "hitting_set_limit": hitting_set_limit, "hitting_sets_truncated": hitting_truncated,
                   "global_position_limit": global_position_limit,
                   "enumeration": "minimal conflicts via verified-entailment supports; components by shared conflicts; "
                                  "local positions = complements of minimal hitting sets (Berge); global positions = products"},
        "inputs": {"seed_statement_ids": seed_ids, "rival_statement_ids": rival_ids,
                   "core_atom_statement_ids": added_cores, "witness_atom_statement_ids": added_witness,
                   "certified_cores": len(cores), "entailment_result_ids": len(rule_ids),
                   "witnesses": len(certified_witnesses),
                   "unconditionally_entailed_statement_ids": unconditional},
        "universe": universe,
        "conflicts": [conflict_evidence[conflict] for conflict in conflicts],
        "components": components,
        "positions": [local_positions[pid] for pid in sorted(local_positions)],
        "global_positions": {"count": global_count, "enumerated": len(global_positions),
                             "truncated": global_count is None or global_count > len(global_positions), "positions": global_positions},
        "matrix": rows,
        "common_ground_candidates": [row["statement_id"] for row in rows if row["classification"] == "common_ground_candidate"],
        "territories": [{"statement_id": row["statement_id"], "routes": row["routes"],
                         "transitive_dependents": row["transitive_dependents"],
                         "in_position_ids": row["in_position_ids"], "out_position_ids": row["out_position_ids"]} for row in splits],
        "classification_counts": dict(sorted(summary_counts.items())),
        "defects": defects,
    }


def format_territory(report: dict[str, Any]) -> str:
    bounds = report["bounds"]
    constrained = [component for component in report["components"] if component["conflicts"]]
    witnessed = [position for position in report["positions"] if position["status"] == "witnessed"]
    lines = [report["scope"], "",
             f"Universe: {bounds['atom_count']} atoms (max {bounds['max_atoms']}{', truncated' if bounds['universe_truncated'] else ''}); "
             f"{len(report['conflicts'])} minimal conflicts from {report['inputs']['certified_cores']} certified cores; "
             f"{report['inputs']['witnesses']} witnesses.",
             f"Components: {len(report['components'])} ({len(constrained)} constrained by a conflict); "
             f"local positions: {len(report['positions'])} ({len(witnessed)} witnessed, "
             f"{len(report['positions']) - len(witnessed)} not known inconsistent).",
             f"Global positions: {report['global_positions']['count']} (enumerated {report['global_positions']['enumerated']}, "
             f"limit {bounds['global_position_limit']}); witnessed: "
             f"{sum(1 for position in report['global_positions']['positions'] if position['status'] == 'witnessed')}.",
             "Root-path rows: " + ", ".join(f"{key} {value}" for key, value in report["classification_counts"].items()), ""]
    for component in constrained:
        lines.append(f"Component {component['index']}: {', '.join(component['atom_ids'])}")
        for conflict in component["conflicts"]:
            lines.append(f"  conflict {conflict['statement_ids']} ({conflict['kind']}; {', '.join(conflict['result_ids'])})")
        for pid in component["position_ids"]:
            position = next(item for item in report["positions"] if item["id"] == pid)
            attested = ", ".join(position["attested_by"]) or "no author covers all atoms"
            lines.append(f"  {pid} [{position['status']}] {position['atom_ids']}; attested by: {attested}")
    if report["territories"]:
        lines += ["", "Territories (split rows, by routes then dependents):"]
        lines += [f"  {row['statement_id']}: routes {row['routes']}, dependents {row['transitive_dependents']}, "
                  f"in {len(row['in_position_ids'])}, out {len(row['out_position_ids'])}" for row in report["territories"]]
    else:
        lines += ["", "Territories: none (no certified conflict separates root-path premises)."]
    if report["common_ground_candidates"]:
        lines += ["", "common_ground candidates (in every position of their component, witnessed, no recorded rival;"
                      " no recorded rival usually means unexamined, not agreed):"]
        stated = {row["statement_id"]: row["stating_authors"] for row in report["matrix"]}
        lines += [f"  {sid} (stated by: {', '.join(stated[sid]) or 'no claim'})" for sid in report["common_ground_candidates"]]
    contested = [row for row in report["matrix"] if row["classification"] == "contested_uncertified"]
    if contested:
        lines += ["", "Contested without certified incompatibility (recorded rivals, no core):"]
        lines += [f"  {row['statement_id']}: " + ", ".join(f"{item['statement_id']} ({item['class']})" for item in row["rivals"]) for row in contested]
    for defect in report["defects"]:
        lines.append(f"DEFECT {defect['kind']}: {defect}")
    return "\n".join(lines)
