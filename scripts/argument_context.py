"""Argument context pack: one bounded, derived view of an existing argument.

Agents currently assemble an argument's context from one `dossier` per premise,
`related`, `frontier`, the Challenge module and hand-read imports. This module
projects that context once, for one argument, from the existing authorities:

* Lean source is authoritative for the advertised theorem's text. Import closure
  is a proximity hint, not proof use; optional Lean proof-term inspection marks
  reachable theorem references separately from unused imports.
* `frontier_report` (authoritative for closure, depth and routes).
* Corpus JSON records (arguments, results, attempts, models, relations,
  candidates, configurations, definitions) for everything else.

Nothing here is stored, nothing is maintained by hand and nothing is certified:
the pack is a navigation aid. It never upgrades a recorded result status into
verification and never infers entailment from a shared statement or import.
"""
from __future__ import annotations

import re
from pathlib import Path
from typing import Any

ID_TOKEN = re.compile(r"(?<![A-Za-z0-9-])[A-Z][A-Z0-9]*(?:-[A-Z0-9]+)+(?![A-Za-z0-9-])")
IMPORT = re.compile(r"^(?:public\s+)?import\s+(\S+)", re.M)
DECLARATION = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|public\s+|protected\s+)?(?:theorem|lemma)\s+(\S+)", re.M)
BOUNDARY = re.compile(r"^(?:/--|@\[|theorem\s|lemma\s|def\s|abbrev\s|structure\s|inductive\s|instance\s|end\s|namespace\s|section\s|open\s|variable\s|noncomputable\s|private\s|public\s|protected\s|--)", re.M)


def module_path(root: Path, module: str) -> Path:
    return root / (module.replace(".", "/") + ".lean")


def lean_imports(root: Path, module: str) -> list[str]:
    path = module_path(root, module)
    if not path.is_file():
        return []
    return IMPORT.findall(path.read_text(encoding="utf-8"))


def import_closure(root: Path, module: str) -> dict[str, int]:
    """Repository modules transitively imported by `module`, with BFS depth (1 = direct)."""
    seen: dict[str, int] = {}
    frontier = [module]
    depth = 0
    while frontier:
        depth += 1
        following = []
        for current in frontier:
            for imported in lean_imports(root, current):
                if imported.startswith("TruthCore") and imported not in seen and imported != module:
                    seen[imported] = depth
                    following.append(imported)
        frontier = following
    return seen


def theorem_blocks(root: Path, module: str) -> list[dict[str, Any]]:
    """Each theorem's verbatim statement text (up to `:=`) in source order, with its line."""
    path = module_path(root, module)
    if not path.is_file():
        return []
    text = path.read_text(encoding="utf-8")
    blocks = []
    for match in DECLARATION.finditer(text):
        start = match.start()
        stop = text.find(":=", match.end())
        nxt = BOUNDARY.search(text, match.end())
        if stop < 0 or (nxt and nxt.start() < stop):
            continue
        blocks.append({"name": match.group(1), "line": text.count("\n", 0, start) + 1,
                       "statement": text[start:stop].rstrip()})
    return blocks


def _short(text: str | None, width: int) -> str:
    text = " ".join((text or "").split())
    return text if len(text) <= width else text[: width - 1].rstrip() + "…"


def resolve_target(target: str, arguments: dict[str, Any], results: dict[str, Any]) -> tuple[str | None, list[str]]:
    """An argument ID, a result ID, or a statement concluded by exactly one argument."""
    if target in arguments:
        return target, []
    if target in results:
        return results[target]["argument_id"], []
    concluding = sorted(aid for aid, argument in arguments.items() if argument["conclusion_statement_id"] == target)
    if len(concluding) == 1:
        return concluding[0], []
    return None, concluding


def classify_result_reuse(root: Path, result: dict[str, Any], results: list[dict[str, Any]],
                          arguments: dict[str, dict[str, Any]], used_theorems: list[str],
                          closure_cache: dict[str, dict[str, int]] | None = None) -> list[dict[str, Any]]:
    """Classify observed proof-term references against imports and the argument graph.

    A graph link means only that the reused conclusion is an explicit premise or
    commitment of this argument. No new edge or proof status is inferred.
    """
    module = result.get("solution_module", "")
    if closure_cache is not None and module in closure_cache:
        closure = closure_cache[module]
    else:
        closure = import_closure(root, module) if module else {}
        if closure_cache is not None:
            closure_cache[module] = closure
    by_module: dict[str, list[dict[str, Any]]] = {}
    for other in results:
        for key in ("solution_module", "challenge_module"):
            if other.get(key):
                by_module.setdefault(other[key], []).append(other)
    graph = arguments.get(result["argument_id"], {})
    graph_premises = set(graph.get("premise_statement_ids", []) + graph.get("commitment_statement_ids", []))
    used = set(used_theorems)
    found: dict[str, dict[str, Any]] = {}
    def add(other: dict[str, Any], imported_module: str | None, depth: int | None) -> None:
        if other["id"] == result["id"]:
            return
        conclusion = arguments.get(other["argument_id"], {}).get("conclusion_statement_id")
        graph_linked = conclusion in graph_premises
        theorem_used = other.get("theorem") in used
        classification = ("theorem-used, graph-linked" if graph_linked else
                          "theorem-used, not in argument graph") if theorem_used else "import only"
        found[other["id"]] = {
            "module": imported_module or other.get("solution_module"), "depth": depth,
            "result_id": other["id"], "argument_id": other["argument_id"],
            "theorem": other.get("theorem"), "status": other.get("status"),
            "graph_linked": graph_linked, "theorem_used": theorem_used,
            "classification": classification,
        }
    for imported_module, depth in closure.items():
        for other in by_module.get(imported_module, []):
            add(other, imported_module, depth)
    for other in results:
        if other.get("theorem") in used and other["id"] not in found:
            add(other, None, None)
    return sorted(found.values(), key=lambda entry: (entry["depth"] is None,
                  entry["depth"] if entry["depth"] is not None else 0, entry["result_id"]))


def lean_reuse_review(root: Path, results: list[dict[str, Any]],
                      arguments: dict[str, dict[str, Any]],
                      proof_uses: dict[str, list[str]]) -> dict[str, Any]:
    """One deterministic, read-only view of inspected result proof dependencies."""
    cache: dict[str, dict[str, int]] = {}
    findings = []
    for result in sorted(results, key=lambda entry: entry["id"]):
        if result.get("theorem") not in proof_uses:
            continue
        for entry in classify_result_reuse(root, result, results, arguments,
                                           proof_uses[result["theorem"]], cache):
            findings.append({"source_result_id": result["id"], **entry})
    classes = ("theorem-used, graph-linked", "theorem-used, not in argument graph", "import only")
    return {
        "authority": "Lean proof-term references; advisory only, not graph or proof certification",
        "summary": {"results_inspected": len(proof_uses),
                    **{key: sum(f["classification"] == key for f in findings) for key in classes}},
        "findings": findings,
    }


def context_pack(root: Path, data: dict[str, list[dict[str, Any]]], report: dict[str, Any], argument_id: str,
                 related: list[dict[str, Any]] | None = None,
                 proof_uses: dict[str, list[str]] | None = None) -> dict[str, Any]:
    """`related` is the existing research-index ranking for the conclusion, passed through unchanged."""
    statements = {entry["id"]: entry for entry in data["statements"]}
    arguments = {entry["id"]: entry for entry in data["arguments"]}
    inferences = {entry["id"]: entry for entry in data["inferences"]}
    definitions = {entry["id"]: entry for entry in data["definitions"]}
    disambiguations = {entry["id"]: entry for entry in data["disambiguations"]}
    results_by_argument: dict[str, list[dict[str, Any]]] = {}
    for result in data["results"]:
        results_by_argument.setdefault(result["argument_id"], []).append(result)
    argument = arguments[argument_id]
    conclusion = argument["conclusion_statement_id"]
    premises = list(argument["premise_statement_ids"])
    commitments = list(argument.get("commitment_statement_ids", []))
    focus = [*premises, *commitments, conclusion]
    focus_set = set(focus)
    transcriptions = report["transcription_results"]
    items = {entry["statement_id"]: entry for entry in report["items"]}

    def result_summary(result: dict[str, Any]) -> dict[str, Any]:
        return {"result_id": result["id"], "argument_id": result["argument_id"], "theorem": result.get("theorem"),
                "status": result.get("status"), "transcription": result["id"] in transcriptions}

    def concluded_by(sid: str) -> list[dict[str, Any]]:
        return [
            {"argument_id": aid, "premise_statement_ids": other["premise_statement_ids"],
             "results": [result_summary(r) for r in results_by_argument.get(aid, [])]}
            for aid, other in sorted(arguments.items())
            if other["conclusion_statement_id"] == sid and aid != argument_id
        ]

    def status(sid: str) -> dict[str, Any]:
        closure = report["closed_statements"].get(sid)
        item = items.get(sid)
        return {"closed": closure, "open_depth": item["depth"] if item and not closure else None,
                "established": sid in report["established_statements"],
                "reaches_root": sid in report["reaching_root_statements"]}

    def statement_entry(sid: str) -> dict[str, Any]:
        record = statements.get(sid, {})
        return {"statement_id": sid, "paraphrase": record.get("paraphrase"),
                "lean_declaration": record.get("lean_declaration"), **status(sid),
                "concluded_by": concluded_by(sid)}

    # --- Lean: authoritative type, companions, and actual reuse --------------
    results = results_by_argument.get(argument_id, [])
    module_to_result = {}
    for result in data["results"]:
        for key in ("solution_module", "challenge_module"):
            if result.get(key):
                module_to_result[result[key]] = result
    lean: list[dict[str, Any]] = []
    for result in results:
        theorem = result.get("theorem", "")
        blocks = theorem_blocks(root, result.get("challenge_module", ""))
        short_name = theorem.rsplit(".", 1)[-1]
        advertised = next((block for block in blocks if block["name"] == short_name), None)
        comparator = _load_json(root / result["comparator_config"]) if result.get("comparator_config") else {}
        checked = {name.rsplit(".", 1)[-1] for name in comparator.get("theorem_names", [])}
        closure = import_closure(root, result.get("solution_module", "")) if result.get("solution_module") else {}
        reused = sorted(
            ({"module": module, "depth": depth, **result_summary(module_to_result[module]),
              # Whether the argument graph also records this reuse: the reused result concludes one of our premises.
              "graph_linked": arguments.get(module_to_result[module]["argument_id"], {}).get("conclusion_statement_id") in set(premises + commitments)}
             for module, depth in closure.items()
             if module in module_to_result and module_to_result[module]["id"] != result["id"]),
            key=lambda entry: (entry["depth"], entry["result_id"]))
        consumers = sorted(
            {other["id"] for other in data["results"] if other["id"] != result["id"] and other.get("solution_module")
             and result.get("solution_module") in lean_imports(root, other["solution_module"])})
        consumer_modules = {r["solution_module"] for r in data["results"] if r["id"] in consumers}
        consumers_depth2 = sorted(
            {other["id"] for other in data["results"] if other["id"] != result["id"] and other["id"] not in consumers
             and other.get("solution_module") and consumer_modules.intersection(lean_imports(root, other["solution_module"]))})
        if proof_uses is not None and theorem in proof_uses:
            reused = classify_result_reuse(root, result, data["results"], arguments, proof_uses[theorem])
            for item in reused:
                item["transcription"] = item["result_id"] in transcriptions
        lean_entry = {
            "result_id": result["id"], "theorem": theorem, "status": result.get("status"),
            "transcription": result["id"] in transcriptions,
            "challenge_path": str(module_path(Path(), result.get("challenge_module", ""))),
            "solution_path": str(module_path(Path(), result.get("solution_module", ""))),
            "advertised_statement": advertised,
            "companion_theorems": [
                {**block, "comparator_checked": block["name"] in checked}
                for block in blocks if block["name"] != short_name
            ],
            "permitted_axioms": comparator.get("permitted_axioms", []),
            "direct_imports": lean_imports(root, result.get("solution_module", "")),
            "reused_results": reused,
            "lean_consumers": consumers,
            "lean_consumers_depth2": consumers_depth2,
        }
        if proof_uses is not None and theorem in proof_uses:
            lean_entry["proof_theorems"] = sorted(set(proof_uses[theorem]))
            lean_entry["proof_use_advisory"] = True
        lean.append(lean_entry)

    # Lean neighbours: other results whose Solution directly imports a non-result module ours imports
    # directly (shared vocabulary). Proximity only: a shared import is not a shared premise.
    own_vocabulary = {module for entry in lean for module in entry["direct_imports"] if module not in module_to_result}
    own_results = {result["id"] for result in results}
    lean_neighbours = []
    if own_vocabulary:
        for other in sorted(data["results"], key=lambda entry: entry["id"]):
            if other["id"] in own_results or not other.get("solution_module"):
                continue
            shared = sorted(own_vocabulary.intersection(lean_imports(root, other["solution_module"])))
            if shared:
                lean_neighbours.append({**result_summary(other), "shared_modules": shared})
        lean_neighbours.sort(key=lambda entry: (-len(entry["shared_modules"]), entry["result_id"]))

    # --- graph neighbourhood --------------------------------------------------
    premise_set = set(premises + commitments)
    premise_siblings = sorted(
        ({"argument_id": aid, "shared_premise_statement_ids": sorted(premise_set.intersection(other["premise_statement_ids"])),
          "conclusion_statement_id": other["conclusion_statement_id"],
          "results": [result_summary(r) for r in results_by_argument.get(aid, [])]}
         for aid, other in arguments.items() if aid != argument_id and premise_set.intersection(other["premise_statement_ids"])),
        key=lambda entry: (-len(entry["shared_premise_statement_ids"]), entry["argument_id"]))
    downstream = sorted(
        ({"argument_id": aid, "conclusion_statement_id": other["conclusion_statement_id"],
          "results": [result_summary(r) for r in results_by_argument.get(aid, [])]}
         for aid, other in arguments.items() if conclusion in other["premise_statement_ids"]),
        key=lambda entry: entry["argument_id"])
    same_bundle = sorted(
        aid for aid, other in arguments.items() if aid != argument_id
        and other["conclusion_statement_id"] == conclusion and set(other["premise_statement_ids"]) == set(premises))
    routes = [route for route in report["routes"]["routes"] if route["argument_id"] == argument_id
              or focus_set.intersection(route["open_premise_statement_ids"])]

    # --- countermodels, rivals and unresolved work ---------------------------
    models = [
        {"model_id": model["id"], "statement_id": evaluation["statement_id"], "value": evaluation["value"],
         "theorem": evaluation["theorem"], "role": _role(evaluation["statement_id"], premises, commitments, conclusion)}
        for model in sorted(data["models"], key=lambda entry: entry["id"])
        for evaluation in model["evaluations"] if evaluation["statement_id"] in focus_set
    ]
    # A model violating a statement is the informative case (countermodel/independence witness); list those first.
    models.sort(key=lambda entry: (entry["value"] != "violates", entry["role"] != "premise", entry["model_id"]))
    relations = [
        {"relation_id": relation["id"], "subject_id": relation["subject_id"], "predicate": relation["predicate"],
         "object_id": relation["object_id"], "note": relation.get("note") or relation.get("basis")}
        for relation in sorted(data["relations"], key=lambda entry: entry["id"])
        if relation["predicate"] in ("alternative_to", "attacks", "refutes")
        and (relation["subject_id"] in focus_set or relation["object_id"] in focus_set or relation["subject_id"] == argument_id)
    ]
    ids = focus_set | {argument_id} | {result["id"] for result in results}
    attempts = [
        {"attempt_id": attempt["id"], "date": attempt["date"], "kind": attempt["kind"], "outcome": attempt["outcome"],
         "statement_ids": [sid for sid in attempt["statement_ids"] if sid in focus_set],
         "summary": attempt["summary"], "blocker": attempt.get("blocker")}
        for attempt in sorted(data["attempts"], key=lambda entry: (entry["date"], entry["id"]), reverse=True)
        if focus_set.intersection(attempt["statement_ids"]) or ids.intersection(attempt.get("evidence", []))
    ]
    pattern = re.compile(r"(?<![A-Z0-9-])(" + "|".join(re.escape(i) for i in sorted(ids, key=len, reverse=True)) + r")(?![A-Z0-9-])")
    candidates = [
        {"candidate_id": candidate["id"], "status": candidate.get("status"), "priority": candidate.get("priority"),
         "mentions": sorted(set(pattern.findall(" ".join(str(candidate.get(f, "")) for f in ("goal", "reason"))))),
         "goal": candidate.get("goal")}
        for candidate in sorted(data["candidates"], key=lambda entry: entry["id"])
        if pattern.search(" ".join(str(candidate.get(f, "")) for f in ("goal", "reason")))
    ]
    configurations = [
        {"configuration_id": case["id"], "semantics_id": case["semantics"]["id"],
         "statement_ids": sorted(focus_set.intersection([case["seed_statement_id"], *case["semantics"]["applications"]]))}
        for case in sorted(data["configurations"], key=lambda entry: entry["id"])
        if focus_set.intersection([case["seed_statement_id"], *case["semantics"]["applications"]])
    ]
    # Other open leaves on the root routes through this argument, most routes first (#962).
    route_leaves: dict[str, int] = {}
    for route in routes:
        for sid in route["open_premise_statement_ids"]:
            if sid not in focus_set:
                route_leaves[sid] = route_leaves.get(sid, 0) + 1
    # Corpus IDs that the scoped attempts cite in prose or evidence, most cited first (#962).
    known = set(statements) | set(arguments) | {r["id"] for r in data["results"]} | {m["id"] for m in data["models"]}
    cited: dict[str, int] = {}
    for attempt in attempts:
        source = next(a for a in data["attempts"] if a["id"] == attempt["attempt_id"])
        tokens = set(ID_TOKEN.findall(" ".join([attempt["summary"], attempt.get("blocker") or ""]))) | set(source.get("evidence", []))
        for token in tokens & known:
            if token not in ids:
                cited[token] = cited.get(token, 0) + 1
    open_premises = [sid for sid in [*premises, *commitments] if not report["closed_statements"].get(sid)]
    unresolved = {
        "open_premise_statement_ids": open_premises,
        "open_premises_without_other_route": [sid for sid in open_premises if not concluded_by(sid)],
        "blocked_or_failed_attempt_ids": [a["attempt_id"] for a in attempts if a["outcome"] in ("blocked", "failed")],
        "transcription_result_ids": [r["id"] for r in results if r["id"] in transcriptions],
        "unchecked_companion_theorems": [f"{entry['result_id']}:{block['name']}" for entry in lean
                                         for block in entry["companion_theorems"] if not block["comparator_checked"]],
    }
    return {
        "argument_id": argument_id,
        "meaning": argument.get("meaning"),
        "root": report["root"],
        "conclusion": statement_entry(conclusion),
        "premises": [statement_entry(sid) for sid in premises],
        "commitments": [statement_entry(sid) for sid in commitments],
        "inferences": [
            {"inference_id": iid, "rule": inferences[iid].get("rule"),
             "input_statement_ids": inferences[iid]["input_statement_ids"],
             "assumption_statement_ids": inferences[iid].get("assumption_statement_ids", []),
             "discharged_statement_ids": inferences[iid].get("discharged_statement_ids", []),
             "output_statement_id": inferences[iid]["output_statement_id"]}
            for iid in argument["inference_ids"] if iid in inferences
        ],
        "lean": lean,
        "downstream_arguments": downstream,
        "premise_sibling_arguments": premise_siblings,
        "lean_neighbours": lean_neighbours,
        "related_statements": [
            {"statement_id": match["statement_id"], "reasons": sorted({reason["kind"] for reason in match.get("reasons", [])})}
            for match in (related or [])
        ],
        "same_bundle_argument_ids": same_bundle,
        "routes": routes,
        "models": models,
        "rival_relations": relations,
        "configurations": configurations,
        "attempts": attempts,
        "candidates": candidates,
        "unresolved": unresolved,
        "route_open_leaves": [sid for sid, _ in sorted(route_leaves.items(), key=lambda item: (-item[1], item[0]))],
        "attempt_cited_ids": [cid for cid, _ in sorted(cited.items(), key=lambda item: (-item[1], item[0]))],
        "definitions": [{"id": did, "definition": definitions[did].get("definition")}
                        for did in argument.get("definition_ids", []) if did in definitions],
        "disambiguations": [{"id": did, "resolution": disambiguations[did].get("resolution")}
                            for did in argument.get("disambiguation_ids", []) if did in disambiguations],
    }


def _role(sid: str, premises: list[str], commitments: list[str], conclusion: str) -> str:
    if sid == conclusion:
        return "conclusion"
    return "premise" if sid in premises else "commitment"


def _load_json(path: Path) -> dict[str, Any]:
    import json
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return {}


def format_context(pack: dict[str, Any], limit: int = 6, width: int = 150, overflow: int = 40) -> str:
    """Compact text for an agent's context window; `--json` keeps every entry untruncated."""
    lines: list[str] = []

    def capped(entries: list[Any], render, ids=None) -> None:
        """Render up to `limit` entries; name the hidden ones by ID only (#962), so a
        truncated section still surfaces what exists without its prose."""
        for entry in entries[:limit]:
            lines.extend(render(entry))
        hidden = entries[limit:]
        if hidden:
            names = list(dict.fromkeys(i for entry in hidden for i in (ids(entry) if ids else [])))
            if names and overflow > 0:
                shown = names[:overflow]
                extra = f" +{len(names) - len(shown)}" if len(names) > len(shown) else ""
                lines.append(f"  … {len(hidden)} more: {', '.join(shown)}{extra} (see --json)")
            else:
                lines.append(f"  … {len(hidden)} more (see --json)")
        if not entries:
            lines.append("  none recorded")

    def status(entry: dict[str, Any]) -> str:
        if entry["closed"]:
            return f"closed ({entry['closed']})"
        return f"open ({entry['open_depth']})" if entry["open_depth"] else "not a frontier premise"

    def routes_of(entry: dict[str, Any]) -> str:
        others = entry["concluded_by"]
        if not others:
            return "no other argument concludes it"
        shown = []
        for other in others[:3]:
            tags = ",".join(sorted({(r["status"] or "?") + ("/transcription" if r["transcription"] else "") for r in other["results"]})) or "no result"
            shown.append(f"{other['argument_id']} [{tags}]")
        more = (" +" + ", ".join(other["argument_id"] for other in others[3:3 + overflow])) if len(others) > 3 else ""
        return "also concluded by " + "; ".join(shown) + more

    lines.append(f"Argument {pack['argument_id']} (derived context; navigation only, not verification)")
    lines.append("  " + _short(pack["meaning"], width * 2))
    c = pack["conclusion"]
    lines.append(f"\nConclusion {c['statement_id']}: {status(c)}; reaches {pack['root']}: {str(c['reaches_root']).lower()}")
    lines.append("  " + _short(c["paraphrase"], width) + f" [Lean {c['lean_declaration']}]")
    lines.append("  " + routes_of(c))
    for label, key in (("Premises", "premises"), ("Commitments", "commitments")):
        if key == "commitments" and not pack[key]:
            continue
        lines.append(f"\n{label} ({len(pack[key])}; every one is required jointly):" if pack[key] else f"\n{label}: none")
        for entry in pack[key]:
            lines.append(f"  {entry['statement_id']}: {status(entry)}; {routes_of(entry)}")
            lines.append("    " + _short(entry["paraphrase"], width) + f" [Lean {entry['lean_declaration']}]")

    lines.append("\nLean (authoritative; text copied from the frozen Challenge module):")
    for entry in pack["lean"]:
        flag = "; TRANSCRIPTION" if entry["transcription"] else ""
        lines.append(f"  result {entry['result_id']} [{entry['status']}{flag}] axioms {entry['permitted_axioms'] or 'none'}")
        lines.append(f"  {entry['challenge_path']}:{(entry['advertised_statement'] or {}).get('line', '?')}  solution {entry['solution_path']}")
        if entry["advertised_statement"]:
            lines.extend("    " + line for line in entry["advertised_statement"]["statement"].splitlines())
        else:
            lines.append(f"    theorem {entry['theorem']} not found in the Challenge source")
        if entry["companion_theorems"]:
            lines.append("  companion theorems in the same Challenge (often countermodels/independence):")
            for block in entry["companion_theorems"][:limit]:
                head = " ".join(block["statement"].split())
                checked = "comparator-checked" if block["comparator_checked"] else "NOT in comparator theorem_names"
                lines.append(f"    L{block['line']} {_short(head, width)} [{checked}]")
            if len(entry["companion_theorems"]) > limit:
                lines.append(f"    … {len(entry['companion_theorems']) - limit} more")
        if entry.get("proof_use_advisory"):
            lines.append("  theorem reuse: Lean proof-term reachability (review only); d = import depth:")
            capped(entry["reused_results"], lambda r: [f"    {r['result_id']} d{r['depth'] if r['depth'] is not None else '?'} "
                f"[{r['status']}; {r['classification']}] {r['theorem']}"],
                ids=lambda r: [r["result_id"]])
        else:
            lines.append("  reuses results through Lean imports (depth 1 = direct; not proof use):")
            capped(entry["reused_results"], lambda r: [f"    {r['result_id']} d{r['depth']} "
                f"[{r['status']}; {'graph-linked' if r['graph_linked'] else 'import only, not an argument premise'}] {r['theorem']}"],
                ids=lambda r: [r["result_id"]])
        lines.append("  results whose Solution imports this Solution: " + (", ".join(entry["lean_consumers"]) or "none"))
        if entry.get("lean_consumers_depth2"):
            second = entry["lean_consumers_depth2"]
            lines.append("  … and whose Solution imports one of those: " + ", ".join(second[:overflow])
                         + (f" +{len(second) - overflow}" if len(second) > overflow else ""))
    if not pack["lean"]:
        lines.append("  no result record: the argument has no checked Lean theorem")

    lines.append("\nInference steps:")
    capped(pack["inferences"], lambda i: [f"  {i['inference_id']} ({i['rule']}): {', '.join(i['input_statement_ids']) or '—'} ⊢ {i['output_statement_id']}"
                                          + (f"; assumes {', '.join(i['assumption_statement_ids'])}" if i["assumption_statement_ids"] else "")])
    lines.append("\nDownstream arguments using the conclusion as a premise:")
    capped(pack["downstream_arguments"], lambda d: [f"  {d['argument_id']} ⊢ {d['conclusion_statement_id']}"],
           ids=lambda d: [d["argument_id"], d["conclusion_statement_id"]])
    lines.append("Arguments sharing a premise (most shared first):")
    capped(pack["premise_sibling_arguments"], lambda d: [
        f"  {d['argument_id']} [{','.join(sorted({r['status'] or '?' for r in d['results']})) or 'no result'}] shares {', '.join(d['shared_premise_statement_ids'])} ⊢ {d['conclusion_statement_id']}"],
        ids=lambda d: [d["argument_id"], d["conclusion_statement_id"]])
    lines.append("Lean neighbours (Solutions importing the same vocabulary modules; proximity, not entailment):")
    capped(pack["lean_neighbours"], lambda n: [f"  {n['result_id']} [{n['status']}] via {', '.join(m.rsplit('.', 1)[-1] for m in n['shared_modules'])}"],
           ids=lambda n: [n["result_id"]])
    if pack["related_statements"]:
        lines.append("Related to the conclusion (research-index ranking; discovery only): "
                     + ", ".join(r["statement_id"] for r in pack["related_statements"][:overflow]))
    if pack["same_bundle_argument_ids"]:
        lines.append("Same premise bundle and conclusion (possible duplicate): " + ", ".join(pack["same_bundle_argument_ids"]))
    lines.append(f"\nRoutes to {pack['root']} touching this argument (cost = open leaves):")
    capped(pack["routes"], lambda r: [f"  {r['argument_id']}: cost {r['cost']}"], ids=lambda r: [r["argument_id"]])
    if pack["route_open_leaves"]:
        leaves = pack["route_open_leaves"]
        lines.append("  other open leaves on these routes (most routes first): " + ", ".join(leaves[:overflow])
                     + (f" +{len(leaves) - overflow}" if len(leaves) > overflow else ""))

    lines.append("\nCountermodels and rivals (formal interpretations; no premise closure):")
    values: dict[str, int] = {}
    for model in pack["models"]:
        values[model["value"]] = values.get(model["value"], 0) + 1
    lines.append("  model evaluations: " + (", ".join(f"{count} {value}" for value, count in sorted(values.items())) or "none registered"))
    violating = [m for m in pack["models"] if m["value"] == "violates"]
    if violating:
        capped(violating, lambda m: [f"  {m['model_id']} violates {m['role']} {m['statement_id']} ({m['theorem']})"],
               ids=lambda m: [m["model_id"]])
    lines.append("  rival relations (alternative_to / attacks / refutes):")
    capped(pack["rival_relations"], lambda r: [f"    {r['relation_id']}: {r['subject_id']} {r['predicate']} {r['object_id']}"],
           ids=lambda r: [r["subject_id"], r["object_id"]])
    if pack["configurations"]:
        lines.append("  configuration cases: " + ", ".join(f"{c['configuration_id']} ({c['semantics_id']})" for c in pack["configurations"]))

    lines.append("\nAttempts on these statements, newest first (outcomes establish nothing):")
    capped(pack["attempts"], lambda a: [f"  {a['attempt_id']} [{a['date']}; {a['kind']}; {a['outcome']}]: {_short(a['summary'], width)}"]
           + ([f"    blocker: {_short(a['blocker'], width)}"] if a["blocker"] else []),
           ids=lambda a: [a["attempt_id"]])
    if pack["attempt_cited_ids"]:
        cited = pack["attempt_cited_ids"]
        lines.append("  IDs these attempts cite (most cited first; discovery only): " + ", ".join(cited[:overflow])
                     + (f" +{len(cited) - overflow}" if len(cited) > overflow else ""))
    lines.append("\nCandidates mentioning these IDs:")
    capped(pack["candidates"], lambda c: [f"  {c['candidate_id']} [{c['status']}; p{c['priority']}] mentions {', '.join(c['mentions'])}: {_short(c['goal'], width)}"],
           ids=lambda c: [c["candidate_id"]])

    u = pack["unresolved"]
    lines.append("\nUnresolved:")
    lines.append("  open premises: " + (", ".join(u["open_premise_statement_ids"]) or "none"))
    lines.append("  open with no other recorded argument: " + (", ".join(u["open_premises_without_other_route"]) or "none"))
    lines.append("  blocked/failed attempts: " + (", ".join(u["blocked_or_failed_attempt_ids"]) or "none"))
    if u["transcription_result_ids"]:
        lines.append("  transcription results (close nothing by themselves): " + ", ".join(u["transcription_result_ids"]))
    if u["unchecked_companion_theorems"]:
        lines.append("  companion theorems not checked by Comparator: " + ", ".join(u["unchecked_companion_theorems"]))

    lines.append("\nTerms linked by the argument (IDs; read with research_index.py show):")
    lines.append("  " + (", ".join(d["id"] for d in pack["definitions"] + pack["disambiguations"]) or "none"))
    lines.append("\nNext: corpus.py dossier <open premise>; corpus.py related <conclusion>; "
                 "scripts/verify-result.sh <result> after lake build.")
    return "\n".join(lines)
