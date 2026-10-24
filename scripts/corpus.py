#!/usr/bin/env python3
"""Small, dependency-free corpus queue/validation tool for truth-core."""

from __future__ import annotations

import argparse
import json
import re
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
    available = set(argument["premise_statement_ids"]) | set(argument.get("commitment_statement_ids", []))
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


# Premise-program schema (#156). A statement may be marked self-evident, and
# relations may record alternatives to a premise, refutations of an alternative,
# and objections attacking a premise. All of it is optional metadata.
ALTERNATIVE_PREDICATE = "alternative_to"
REFUTES_PREDICATE = "refutes"
ATTACKS_PREDICATE = "attacks"
# Source evidence bearing on a premise (claim → statement). It records where the
# premise is defended from a text; it is not an inference and closes nothing.
SUPPORTS_PREDICATE = "supports"
# Designated route (argument → statement; owner decision on #143, 2026-10-24):
# when a statement has root_route relations, `frontier` walks up into it only
# through the designated arguments, so premises of other arguments for the same
# conclusion do not reach the root through it.
ROOT_ROUTE_PREDICATE = "root_route"
DEFAULT_FRONTIER_ROOT = "STMT-CATHOLICISM-TRUE"
# Depth of an open premise (#143, 2026-10-24): "bare" when no claim states it
# and no `supports` relation points to it; otherwise "sourced" (sourced but not
# yet defended). The aim is to drive bare premises to zero, then defend the rest.
FRONTIER_BARE = "bare"
FRONTIER_SOURCED = "sourced"


def validate_self_evident(
    path: Path,
    statement: dict[str, Any],
    claim_ids: set[str],
    result_ids: set[str],
) -> None:
    marking = statement.get("self_evident")
    if marking is None:
        return
    if not isinstance(marking, dict):
        raise CorpusError(
            f"{path.relative_to(ROOT)}: self_evident must be an object with justification_ids"
        )
    justification = require_string_list(marking, "justification_ids", path, allow_empty=False)
    for justification_id in justification:
        if justification_id not in claim_ids and justification_id not in result_ids:
            raise CorpusError(
                f"{path.relative_to(ROOT)}: self_evident justification {justification_id} "
                "is neither a claim id nor a result id"
            )


def validate_premise_program_relation(path: Path, relation: dict[str, Any]) -> None:
    predicate = relation["predicate"]
    expected = {
        ALTERNATIVE_PREDICATE: ({"statement"}, "statement"),
        REFUTES_PREDICATE: ({"argument"}, "statement"),
        ATTACKS_PREDICATE: ({"statement", "claim", "argument"}, "statement"),
        SUPPORTS_PREDICATE: ({"claim"}, "statement"),
        ROOT_ROUTE_PREDICATE: ({"argument"}, "statement"),
    }.get(predicate)
    if expected is None:
        return
    subject_kinds, object_kind = expected
    if relation["subject_kind"] not in subject_kinds or relation["object_kind"] != object_kind:
        raise CorpusError(
            f"{path.relative_to(ROOT)}: {predicate} relates "
            f"{'/'.join(sorted(subject_kinds))} to {object_kind}"
        )


def frontier_report(
    statements: list[dict[str, Any]],
    arguments: list[dict[str, Any]],
    results: list[dict[str, Any]],
    relations: list[dict[str, Any]],
    root: str | None = DEFAULT_FRONTIER_ROOT,
    transcription: list[dict[str, Any]] | None = None,
    claims: list[dict[str, Any]] | None = None,
) -> dict[str, Any]:
    """Open premises: used as an argument premise and not closed. A statement
    is closed when it is (a) the conclusion of a verified result that is not a
    transcription (invariant 16), (b) marked self_evident, (c) refuted in every
    one of its recorded alternatives (at least one alternative recorded), or
    (d) the conclusion of a transcription result all of whose argument premises
    are closed (#143, 2026-10-24). Rule (d) is applied to a fixpoint.

    Each open premise also gets a depth (#143, 2026-10-24): "bare" when no
    claim states it and no `supports` relation points to it, otherwise
    "sourced" (sourced but undefended)."""
    statement_by_id = {statement["id"]: statement for statement in statements}
    argument_by_id = {argument["id"]: argument for argument in arguments}
    verified_arguments = {result["argument_id"] for result in results}
    # Invariant 16: a transcription closes no frontier node. A conclusion is
    # closed only by a verified result that is not a single application of one
    # hypothesis (the rule /graph uses for its "transcription" status).
    transcription_results = {
        flag["result_id"] for flag in (transcription or []) if flag["single_application_of"]
    }
    verified_conclusions = {
        argument_by_id[result["argument_id"]]["conclusion_statement_id"]
        for result in results
        if result["argument_id"] in argument_by_id and result["id"] not in transcription_results
    }
    transcription_only_conclusions = {
        argument_by_id[result["argument_id"]]["conclusion_statement_id"]
        for result in results
        if result["argument_id"] in argument_by_id
    } - verified_conclusions

    dependents: dict[str, set[str]] = {}
    for argument in arguments:
        for premise in argument["premise_statement_ids"]:
            dependents.setdefault(premise, set()).add(argument["id"])

    alternatives: dict[str, set[str]] = {}
    refuted: set[str] = set()
    objections: dict[str, set[str]] = {}
    support: dict[str, set[str]] = {}
    routes: dict[str, set[str]] = {}
    for relation in relations:
        predicate = relation.get("predicate")
        if predicate == ALTERNATIVE_PREDICATE:
            alternatives.setdefault(relation["object_id"], set()).add(relation["subject_id"])
        elif predicate == REFUTES_PREDICATE and relation["subject_id"] in verified_arguments:
            refuted.add(relation["object_id"])
        elif predicate == ATTACKS_PREDICATE:
            objections.setdefault(relation["object_id"], set()).add(
                f"{relation['subject_kind']}:{relation['subject_id']}"
            )
        elif predicate == SUPPORTS_PREDICATE:
            support.setdefault(relation["object_id"], set()).add(relation["subject_id"])
        elif predicate == ROOT_ROUTE_PREDICATE:
            routes.setdefault(relation["object_id"], set()).add(relation["subject_id"])

    def upward(statement_id: str) -> tuple[list[str], list[str], list[str] | None]:
        """Breadth-first walk from a premise through the arguments that use it.
        Returns dependent arguments and conclusions (by distance, then id) and
        one shortest statement/argument path to the root, if reachable."""
        seen_arguments: list[str] = []
        seen_statements: list[str] = []
        visited_arguments: set[str] = set()
        visited_statements = {statement_id}
        parent: dict[str, tuple[str, str]] = {}
        frontier = [statement_id]
        while frontier:
            next_frontier: list[str] = []
            layer: list[tuple[str, str, str]] = []
            for current in frontier:
                for argument_id in dependents.get(current, ()):
                    conclusion = argument_by_id[argument_id]["conclusion_statement_id"]
                    layer.append((argument_id, conclusion, current))
            for argument_id, conclusion, current in sorted(layer):
                if argument_id not in visited_arguments:
                    visited_arguments.add(argument_id)
                    seen_arguments.append(argument_id)
                # root_route: a routed conclusion is entered only through its
                # designated arguments.
                if conclusion in routes and argument_id not in routes[conclusion]:
                    continue
                if conclusion not in visited_statements:
                    visited_statements.add(conclusion)
                    parent[conclusion] = (argument_id, current)
                    seen_statements.append(conclusion)
                    next_frontier.append(conclusion)
            frontier = sorted(next_frontier)
        path: list[str] | None = None
        if root is not None and root in parent:
            path = [root]
            node = root
            while node != statement_id:
                argument_id, node = parent[node]
                path[:0] = [node, argument_id]
        return seen_arguments, seen_statements, path

    def defended(statement_id: str) -> bool:
        recorded = alternatives.get(statement_id, ())
        return bool(recorded) and all(alternative in refuted for alternative in recorded)

    closed = {
        statement_id
        for statement_id in statement_by_id.keys() | dependents.keys() | verified_conclusions
        if statement_id in verified_conclusions
        or statement_by_id.get(statement_id, {}).get("self_evident") is not None
        or defended(statement_id)
    }
    # Rule (d): a transcription still closes nothing by itself, but it carries
    # closure from its premises to its conclusion. Iterate to a fixpoint; each
    # pass visits the transcription results in ID order, so the recorded result
    # for a conclusion is deterministic.
    transcription_steps = sorted(
        (result["id"], argument_by_id[result["argument_id"]])
        for result in results
        if result["id"] in transcription_results and result["argument_id"] in argument_by_id
    )
    closed_via_transcription: dict[str, dict[str, Any]] = {}
    changed = True
    while changed:
        changed = False
        for result_id, argument in transcription_steps:
            conclusion = argument["conclusion_statement_id"]
            if conclusion in closed:
                continue
            premises = argument["premise_statement_ids"]
            if all(premise in closed for premise in premises):
                closed.add(conclusion)
                closed_via_transcription[conclusion] = {
                    "statement_id": conclusion,
                    "result_id": result_id,
                    "argument_id": argument["id"],
                    "premise_statement_ids": sorted(set(premises)),
                }
                changed = True

    # Why each closed statement is closed, for views such as the explorer's
    # state page (#200). The first matching rule wins, in the order (a)-(d).
    closed_statements: dict[str, str] = {}
    for statement_id in sorted(closed):
        if statement_id in verified_conclusions:
            closed_statements[statement_id] = "proved"
        elif statement_by_id.get(statement_id, {}).get("self_evident") is not None:
            closed_statements[statement_id] = "self_evident"
        elif defended(statement_id):
            closed_statements[statement_id] = "alternatives_refuted"
        else:
            closed_statements[statement_id] = "via_transcription"

    # Closed is a per-node property: a proved statement may still rest on open
    # premises (the skeleton proves the root from nine of them). A statement is
    # *established* when it is self-evident or defended, or is the conclusion of
    # a verified result (transcriptions included) whose premises are all
    # established. Computed as a least fixpoint; it adds no closure rule.
    established = {
        statement_id
        for statement_id in statement_by_id
        if statement_by_id[statement_id].get("self_evident") is not None or defended(statement_id)
    }
    verified_steps = [
        argument_by_id[result["argument_id"]] for result in results if result["argument_id"] in argument_by_id
    ]
    changed = True
    while changed:
        changed = False
        for argument in verified_steps:
            conclusion = argument["conclusion_statement_id"]
            if conclusion not in established and all(
                premise in established for premise in argument["premise_statement_ids"]
            ):
                established.add(conclusion)
                changed = True

    stating_claims: dict[str, set[str]] = {}
    for claim in claims or []:
        stating_claims.setdefault(claim["statement_id"], set()).add(claim["id"])

    items: list[dict[str, Any]] = []
    for statement_id in sorted(dependents):
        if statement_id in closed:
            continue
        recorded = sorted(alternatives.get(statement_id, ()))
        all_arguments, all_conclusions, path = upward(statement_id)
        items.append(
            {
                "statement_id": statement_id,
                "paraphrase": statement_by_id.get(statement_id, {}).get("paraphrase", ""),
                "transcription_only": statement_id in transcription_only_conclusions,
                "dependent_arguments": sorted(dependents[statement_id]),
                "transitive_dependent_arguments": all_arguments,
                "transitive_dependent_statements": all_conclusions,
                "path_to_root": path,
                "alternatives": [
                    {"statement_id": alternative, "refuted": alternative in refuted}
                    for alternative in recorded
                ],
                "objections": sorted(objections.get(statement_id, ())),
                "supporting_claims": sorted(support.get(statement_id, ())),
                "stating_claims": sorted(stating_claims.get(statement_id, ())),
                "depth": (
                    FRONTIER_SOURCED
                    if stating_claims.get(statement_id) or support.get(statement_id)
                    else FRONTIER_BARE
                ),
            }
        )
    items.sort(
        key=lambda item: (
            item["path_to_root"] is None,
            -len(item["transitive_dependent_arguments"]),
            -len(item["dependent_arguments"]),
            item["statement_id"],
        )
    )
    goal_premise_arguments: dict[str, list[str]] = {}
    for flag in transcription or []:
        for premise in flag["goal_consequent_premises"]:
            for statement_id in premise["statement_ids"]:
                goal_premise_arguments.setdefault(statement_id, []).append(flag["argument_id"])
    for item in items:
        item["transcription_premise_of"] = sorted(goal_premise_arguments.get(item["statement_id"], []))
    closures: list[dict[str, Any]] = []
    for statement_id in sorted(closed_via_transcription):
        _, _, path = upward(statement_id)
        closures.append({**closed_via_transcription[statement_id], "path_to_root": path})
    return {
        "root": root,
        "root_known": root is not None and root in statement_by_id,
        "transcription_flags": transcription or [],
        "closed_via_transcription": closures,
        "closed_statements": closed_statements,
        "established_statements": sorted(established),
        "alternatives_recorded": bool(alternatives),
        "open_premise_count": len(items),
        "depth_counts": depth_counts(items),
        "items": items,
    }


def depth_counts(items: list[dict[str, Any]]) -> dict[str, int]:
    """Open premises by depth: bare vs. sourced but undefended."""
    return {
        depth: sum(1 for item in items if item["depth"] == depth)
        for depth in (FRONTIER_BARE, FRONTIER_SOURCED)
    }


# Transcription heuristics (#156 review). Many results only transcribe a bridge
# premise "A ∧ B → C" whose consequent is the goal. These checks read the Lean
# sources textually, so they are deterministic heuristics, not proofs: they can
# miss a transcription hidden behind further definitions, and a flagged proof
# can still be a faithful one-step argument.
SHORT_PROOF_STEPS = 2
OPEN_BRACKETS = "([{⟨"
CLOSE_BRACKETS = ")]}⟩"
LEAN_DEF_RE = re.compile(r"^(?:noncomputable\s+)?(?:def|abbrev)\s+([A-Za-z_][\w.']*)", re.MULTILINE)
LEAN_THEOREM_RE = re.compile(r"^theorem\s+([A-Za-z_][\w.']*)", re.MULTILINE)
LEAN_IDENT_RE = re.compile(r"[A-Za-z_][\w.']*")


def strip_lean_comments(text: str) -> str:
    text = re.sub(r"/-.*?-/", " ", text, flags=re.DOTALL)
    return re.sub(r"--[^\n]*", "", text)


def split_top_level(text: str, separator: str) -> list[str]:
    parts: list[str] = []
    depth = 0
    start = 0
    index = 0
    while index < len(text):
        char = text[index]
        if char in OPEN_BRACKETS:
            depth += 1
        elif char in CLOSE_BRACKETS:
            depth -= 1
        elif depth == 0 and text.startswith(separator, index):
            parts.append(text[start:index])
            start = index + len(separator)
            index = start
            continue
        index += 1
    parts.append(text[start:])
    return [" ".join(part.split()) for part in parts]


def lean_declarations() -> tuple[dict[str, tuple[list[str], str]], dict[str, str]]:
    """Definitions (explicit parameter names, body) and theorem source blocks,
    keyed by the declaration's last name component."""
    definitions: dict[str, tuple[list[str], str]] = {}
    theorems: dict[str, str] = {}
    for path in sorted((ROOT / "TruthCore").rglob("*.lean")):
        text = strip_lean_comments(path.read_text(encoding="utf-8"))
        for match in LEAN_DEF_RE.finditer(text):
            block = declaration_block(text, match.end())
            header, separator, body = block.partition(":=")
            if not separator:
                continue
            params = explicit_parameters(header)
            signature_type = header_type(header)
            if signature_type is None:
                continue
            definitions.setdefault(match.group(1).rsplit(".", 1)[-1], (params, " ".join(body.split())))
        for match in LEAN_THEOREM_RE.finditer(text):
            theorems.setdefault(match.group(1).rsplit(".", 1)[-1], declaration_block(text, match.end()))
    return definitions, theorems


def declaration_block(text: str, start: int) -> str:
    """Text up to the next line that starts at column 0."""
    match = re.search(r"\n(?=\S)", text[start:])
    return text[start : start + match.start()] if match else text[start:]


def binder_groups(header: str) -> tuple[list[tuple[str, list[str], str]], str]:
    groups: list[tuple[str, list[str], str]] = []
    rest = header.strip()
    while rest and rest[0] in "({[":
        depth = 0
        end = len(rest) - 1
        for index, char in enumerate(rest):
            if char in OPEN_BRACKETS:
                depth += 1
            elif char in CLOSE_BRACKETS:
                depth -= 1
                if depth == 0:
                    end = index
                    break
        inner = rest[1:end]
        names, _, binder_type = inner.partition(":")
        groups.append((rest[0], names.split(), " ".join(binder_type.split())))
        rest = rest[end + 1 :].strip()
    return groups, rest


def explicit_parameters(header: str) -> list[str]:
    groups, _ = binder_groups(header)
    return [name for bracket, names, _ in groups if bracket == "(" for name in names]


def header_type(header: str) -> str | None:
    _, rest = binder_groups(header)
    if not rest.startswith(":"):
        return None
    return " ".join(rest[1:].split())


def unfold_once(expression: str, definitions: dict[str, tuple[list[str], str]]) -> str:
    """Unfold a head definition applied to identifier arguments, one level."""
    tokens = expression.split()
    if not tokens:
        return expression
    head = tokens[0].rsplit(".", 1)[-1]
    if head not in definitions:
        return expression
    params, body = definitions[head]
    args = tokens[1:]
    if len(args) != len(params) or not all(LEAN_IDENT_RE.fullmatch(arg) for arg in args):
        return expression
    mapping = dict(zip(params, args))
    return LEAN_IDENT_RE.sub(lambda m: mapping.get(m.group(0), m.group(0)), body)


def strip_quantifier_prefix(expression: str) -> str:
    expression = expression.strip()
    while expression.startswith("∀"):
        parts = split_top_level(expression, ",")
        if len(parts) < 2:
            break
        expression = ",".join(parts[1:]).strip()
    while expression.startswith("(") and expression.endswith(")"):
        inner = expression[1:-1]
        if split_top_level(inner, ")")[0] != " ".join(inner.split()):
            break
        expression = inner.strip()
    return " ".join(expression.split())


def consequent(expression: str) -> str | None:
    parts = split_top_level(strip_quantifier_prefix(expression), "→")
    return strip_quantifier_prefix(parts[-1]) if len(parts) > 1 else None


def transcription_flags(
    results: list[dict[str, Any]],
    arguments: list[dict[str, Any]],
    statements: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    """For each result: hypotheses whose consequent is syntactically the goal
    (after one level of unfolding), and whether the proof is a single
    application of a hypothesis."""
    definitions, theorems = lean_declarations()
    argument_by_id = {argument["id"]: argument for argument in arguments}
    declaration_tail = {
        statement["id"]: statement["lean_declaration"].rsplit(".", 1)[-1]
        for statement in statements
        if statement.get("lean_declaration")
    }
    flags: list[dict[str, Any]] = []
    for result in sorted(results, key=lambda record: record["id"]):
        solution = module_path(result["solution_module"])
        name = result["theorem"].rsplit(".", 1)[-1]
        if not solution.is_file():
            continue
        text = strip_lean_comments(solution.read_text(encoding="utf-8"))
        match = re.search(rf"^theorem\s+{re.escape(name)}\b", text, re.MULTILINE)
        if not match:
            continue
        block = declaration_block(text, match.end())
        header, _, proof = block.partition(":=")
        groups, rest = binder_groups(header)
        goal = " ".join(rest[1:].split()) if rest.startswith(":") else ""
        goal_forms = {strip_quantifier_prefix(goal), strip_quantifier_prefix(unfold_once(goal, definitions))}
        hypotheses = [(n, kind) for bracket, names, kind in groups if bracket == "(" for n in names]
        premises = argument_by_id.get(result["argument_id"], {}).get("premise_statement_ids", [])
        goal_premises: list[dict[str, Any]] = []
        for hypothesis, kind in hypotheses:
            if not kind or kind.endswith("Prop") or kind.endswith("Type"):
                continue
            ends = {consequent(kind), consequent(unfold_once(kind, definitions))} - {None}
            if ends & goal_forms:
                head = kind.split()[0].rsplit(".", 1)[-1]
                statement_ids = sorted(sid for sid in premises if declaration_tail.get(sid) == head)
                goal_premises.append({"hypothesis": hypothesis, "statement_ids": statement_ids})
        hypothesis_names = {hypothesis for hypothesis, _ in hypotheses}
        proof = proof.strip()
        # A term-mode proof is one expression even when it spans several lines
        # (same rule as apps/corpus-explorer/src/lib/lean-transcription.ts).
        raw_steps = proof.splitlines() if re.match(r"by\b", proof) else [" ".join(proof.split())]
        steps = [line.strip() for line in raw_steps if line.strip() and line.strip() != "by"]
        if steps and steps[0].startswith("by "):
            steps[0] = steps[0][3:].strip()
        single = None
        applied = [step for step in steps if not re.match(r"intros?\b", step)]
        if len(applied) == 1:
            step = applied[0].removeprefix("exact ").strip()
            head = LEAN_IDENT_RE.match(step)
            if head and head.group(0).split(".", 1)[0] in hypothesis_names:
                single = head.group(0).split(".", 1)[0]
        short = len(steps) <= SHORT_PROOF_STEPS
        if goal_premises or single or short:
            flags.append(
                {
                    "result_id": result["id"],
                    "argument_id": result["argument_id"],
                    "proof_steps": len(steps),
                    "single_application_of": single,
                    "goal_consequent_premises": goal_premises,
                }
            )
    return flags


def format_frontier(report: dict[str, Any]) -> str:
    lines: list[str] = []
    root = report["root"]
    root_note = root if report["root_known"] else f"{root} (unknown statement)"
    counts = report["depth_counts"]
    lines.append(
        f"frontier: {report['open_premise_count']} open premises: "
        f"{counts[FRONTIER_BARE]} bare, {counts[FRONTIER_SOURCED]} sourced-undefended; root {root_note}"
    )
    if not report["alternatives_recorded"]:
        lines.append("alternatives: no alternatives recorded")
    for item in report["items"]:
        lines.append("")
        lines.append(f"{item['statement_id']} [{item['depth']}]")
        if item["paraphrase"]:
            lines.append(f"  {item['paraphrase']}")
        if item.get("transcription_only"):
            lines.append("  open although proved: every verifying result is a transcription (invariant 16)")
        lines.append(
            f"  dependent arguments: {len(item['dependent_arguments'])} "
            f"({', '.join(item['dependent_arguments'])})"
        )
        lines.append(
            f"  transitive dependents: {len(item['transitive_dependent_arguments'])} arguments, "
            f"{len(item['transitive_dependent_statements'])} statements"
        )
        if item["path_to_root"] is None:
            lines.append("  path to root: not reached")
        else:
            lines.append(f"  path to root: {' -> '.join(item['path_to_root'])}")
        if item["alternatives"]:
            rendered = ", ".join(
                f"{alt['statement_id']} ({'refuted' if alt['refuted'] else 'open'})"
                for alt in item["alternatives"]
            )
            lines.append(f"  alternatives: {rendered}")
        elif report["alternatives_recorded"]:
            lines.append("  alternatives: none recorded")
        objections = item["objections"]
        lines.append(f"  objections: {', '.join(objections) if objections else 'none recorded'}")
        if item.get("stating_claims"):
            lines.append("  stating source claims: " + ", ".join(item["stating_claims"]))
        if item.get("supporting_claims"):
            lines.append("  supporting source claims: " + ", ".join(item["supporting_claims"]))
        if item.get("transcription_premise_of"):
            lines.append(
                "  transcription premise of: " + ", ".join(item["transcription_premise_of"])
            )
    closures = report.get("closed_via_transcription", [])
    lines.append("")
    lines.append(
        f"closed via transcription from closed premises: {len(closures)} statements "
        "(a transcription result whose premises are all closed)"
    )
    for closure in closures:
        lines.append(
            f"  {closure['statement_id']}: closed via transcription {closure['result_id']} "
            f"from closed premises ({', '.join(closure['premise_statement_ids']) or 'none'})"
        )
    flags = report.get("transcription_flags", [])
    lines.append("")
    lines.append(
        f"transcription heuristics: {len(flags)} results flagged "
        f"(single application, goal as premise consequent, or at most {SHORT_PROOF_STEPS} proof steps)"
    )
    for flag in flags:
        notes = [f"{flag['proof_steps']} steps"]
        if flag["single_application_of"]:
            notes.append(f"single application of {flag['single_application_of']}")
        for premise in flag["goal_consequent_premises"]:
            ids = ", ".join(premise["statement_ids"]) or "no statement match"
            notes.append(f"goal is consequent of {premise['hypothesis']} ({ids})")
        lines.append(f"  {flag['result_id']}: {'; '.join(notes)}")
    return "\n".join(lines)


# Definitions and disambiguations (#204). A reviewer who says "that depends on
# what the word means" must find the meaning in the repository. A definition
# fixes one sense of a term and is either sourced (claims whose passages give
# it) or explicitly stipulative (with a note saying why and what would source
# it). A disambiguation lists two or more senses of one term and says which
# sense each use takes and why no argument passes from one sense to another.
# Statements, claims and arguments link the senses they use through
# `definition_ids`, and an ambiguity they must be read against through
# `disambiguation_ids`.
DEFINITION_PREFIX = "DEF-"
DISAMBIGUATION_PREFIX = "DISAMB-"
DEFINITION_BASES = {"sourced", "stipulative"}


def lean_tail_exists(path: Path, declaration: Any, all_lean: str) -> None:
    if not isinstance(declaration, str) or not declaration:
        raise CorpusError(
            f"{path.relative_to(ROOT)}: lean_declaration must be a non-empty string when present"
        )
    tail = declaration.rsplit(".", 1)[-1]
    if tail not in all_lean:
        raise CorpusError(
            f"{path.relative_to(ROOT)}: Lean declaration tail {tail!r} was not found under TruthCore/"
        )


def validate_definition(
    path: Path,
    definition: dict[str, Any],
    claim_ids: set[str],
    all_lean: str,
) -> None:
    require(definition, ["id", "term", "definition", "basis"], path)
    if not definition["id"].startswith(DEFINITION_PREFIX):
        raise CorpusError(f"{path.relative_to(ROOT)}: definition id must start with {DEFINITION_PREFIX}")
    basis = definition["basis"]
    if basis not in DEFINITION_BASES:
        raise CorpusError(
            f"{path.relative_to(ROOT)}: basis must be one of {', '.join(sorted(DEFINITION_BASES))}"
        )
    sources = (
        require_string_list(definition, "claim_ids", path, allow_empty=basis != "sourced")
        if "claim_ids" in definition or basis == "sourced"
        else []
    )
    for claim_id in sources:
        if claim_id not in claim_ids:
            raise CorpusError(f"{path.relative_to(ROOT)}: unknown claim id {claim_id}")
    if basis == "stipulative" and not definition.get("note"):
        raise CorpusError(
            f"{path.relative_to(ROOT)}: a stipulative definition needs a note saying why it is "
            "stipulated and what would source it"
        )
    if "lean_declaration" in definition:
        lean_tail_exists(path, definition["lean_declaration"], all_lean)


def validate_disambiguation(
    path: Path,
    disambiguation: dict[str, Any],
    definition_ids: set[str],
) -> None:
    require(disambiguation, ["id", "term", "resolution"], path)
    if not disambiguation["id"].startswith(DISAMBIGUATION_PREFIX):
        raise CorpusError(
            f"{path.relative_to(ROOT)}: disambiguation id must start with {DISAMBIGUATION_PREFIX}"
        )
    senses = require_string_list(disambiguation, "sense_definition_ids", path, allow_empty=False)
    if len(set(senses)) < 2:
        raise CorpusError(f"{path.relative_to(ROOT)}: a disambiguation needs at least two distinct senses")
    for sense in senses:
        if sense not in definition_ids:
            raise CorpusError(f"{path.relative_to(ROOT)}: unknown sense definition id {sense}")


PROSE_ID_RE = re.compile(r"\b(?:STMT|DEF|DISAMB)-[A-Z0-9]+(?:-[A-Z0-9]+)*\b")


def validate_prose_ids(path: Path, record: dict[str, Any], fields: Iterable[str], known: set[str]) -> None:
    """Statement, definition and disambiguation ids cited in prose must exist, so they can be found."""
    for field in fields:
        for cited in PROSE_ID_RE.findall(str(record.get(field, ""))):
            if cited not in known:
                raise CorpusError(f"{path.relative_to(ROOT)}: {field} cites unknown id {cited}")


def validate_term_links(
    path: Path,
    record: dict[str, Any],
    definition_ids: set[str],
    disambiguation_ids: set[str],
) -> list[str]:
    """Check a record's definition and disambiguation links; return its definition ids."""
    linked: list[str] = []
    for field, known in (("definition_ids", definition_ids), ("disambiguation_ids", disambiguation_ids)):
        if field not in record:
            continue
        ids = require_string_list(record, field, path, allow_empty=False)
        for linked_id in ids:
            if linked_id not in known:
                raise CorpusError(f"{path.relative_to(ROOT)}: unknown {field[:-4]} id {linked_id}")
        if field == "definition_ids":
            linked = ids
    return linked


def validate_argument_senses(
    path: Path,
    argument: dict[str, Any],
    statement_index: dict[str, tuple[Path, dict[str, Any]]],
    disambiguations: list[tuple[Path, dict[str, Any]]],
) -> None:
    """An argument whose records use two senses of one ambiguous term must link its disambiguation.

    Mixing senses is not wrong in itself (a premise may connect them), but the
    argument must point the reviewer at the resolution that says why it does
    not equivocate.
    """
    ids = [
        argument["conclusion_statement_id"],
        *argument.get("premise_statement_ids", []),
        *argument.get("commitment_statement_ids", []),
    ]
    senses = set(argument.get("definition_ids", []))
    for statement_id in ids:
        senses.update(statement_index[statement_id][1].get("definition_ids", []))
    linked = set(argument.get("disambiguation_ids", []))
    for _, disambiguation in disambiguations:
        used = senses & set(disambiguation["sense_definition_ids"])
        if len(used) > 1 and disambiguation["id"] not in linked:
            raise CorpusError(
                f"{path.relative_to(ROOT)}: uses senses {', '.join(sorted(used))} of "
                f"'{disambiguation['term']}' but does not link {disambiguation['id']}"
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
    definitions = load_dir("definitions")
    disambiguations = load_dir("disambiguations")

    source_index = index_by_id(sources, "source")
    statement_index = index_by_id(statements, "statement")
    claim_index = index_by_id(claims, "claim")
    inference_index = index_by_id(inferences, "inference")
    argument_index = index_by_id(arguments, "argument")
    relation_index = index_by_id(relations, "relation")
    candidate_index = index_by_id(candidates, "candidate")
    result_index = index_by_id(results, "result")
    definition_index = index_by_id(definitions, "definition")
    disambiguation_index = index_by_id(disambiguations, "disambiguation")
    definition_ids = set(definition_index)
    disambiguation_ids = set(disambiguation_index)
    used_definitions: set[str] = set()

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

    claim_ids = set(claim_index)
    result_ids = set(result_index)

    all_lean = "\n".join(
        path.read_text(encoding="utf-8")
        for path in sorted((ROOT / "TruthCore").rglob("*.lean"))
    )

    declared_by: dict[str, str] = {}
    for path, statement in statements:
        require(statement, ["id", "paraphrase"], path)
        declaration = statement.get("lean_declaration")
        if declaration is not None:
            lean_tail_exists(path, declaration, all_lean)
            # Unique statement identity (owner decision on #143, 2026-10-24):
            # bind-check matches statements by head constant, so one Lean
            # declaration must name exactly one statement ID.
            other = declared_by.setdefault(declaration, statement["id"])
            if other != statement["id"]:
                raise CorpusError(
                    f"{path.relative_to(ROOT)}: lean_declaration {declaration} is already "
                    f"the declaration of statement {other}; each statement needs its own"
                )
        validate_self_evident(path, statement, claim_ids, result_ids)
        used_definitions.update(validate_term_links(path, statement, definition_ids, disambiguation_ids))

    citable = set(statement_index) | definition_ids | disambiguation_ids
    for path, definition in definitions:
        validate_definition(path, definition, claim_ids, all_lean)
        validate_prose_ids(path, definition, ("definition", "note"), citable)
    for path, disambiguation in disambiguations:
        validate_disambiguation(path, disambiguation, definition_ids)
        validate_prose_ids(path, disambiguation, ("resolution",), citable)
        used_definitions.update(disambiguation["sense_definition_ids"])

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
        used_definitions.update(validate_term_links(path, claim, definition_ids, disambiguation_ids))

    for path, inference in inferences:
        require(
            inference,
            ["id", "output_statement_id", "rule", "meaning"],
            path,
        )
        # An inference with no inputs proves its output outright (a theorem of
        # logic, e.g. LOGIC-EXCLUDED-MIDDLE-IRREFUTABLE, #167).
        inputs = require_string_list(inference, "input_statement_ids", path)
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
            ["id", "conclusion_statement_id", "inference_ids", "meaning"],
            path,
        )
        # A consistency argument lists the commitments it shows jointly
        # satisfiable (#160); an argument without premises advertises either
        # such a consistency claim or a theorem of logic (#167).
        commitments = (
            require_string_list(argument, "commitment_statement_ids", path)
            if "commitment_statement_ids" in argument
            else []
        )
        premises = require_string_list(argument, "premise_statement_ids", path)
        inference_ids = require_string_list(argument, "inference_ids", path, allow_empty=False)
        for statement_id in [*premises, *commitments, argument["conclusion_statement_id"]]:
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
        used_definitions.update(validate_term_links(path, argument, definition_ids, disambiguation_ids))
        validate_argument_senses(path, argument, statement_index, disambiguations)

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
        validate_premise_program_relation(path, relation)
        if relation["predicate"] == ROOT_ROUTE_PREDICATE:
            routed = argument_index[relation["subject_id"]][1]["conclusion_statement_id"]
            if routed != relation["object_id"]:
                raise CorpusError(
                    f"{path.relative_to(ROOT)}: root_route argument {relation['subject_id']} "
                    f"concludes {routed}, not {relation['object_id']}"
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

    unused = sorted(definition_ids - used_definitions)
    if unused:
        raise CorpusError(
            "definition(s) linked from no statement, claim or argument and not a sense of "
            f"any disambiguation: {', '.join(unused)}"
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
        "definitions": len(definition_index),
        "disambiguations": len(disambiguation_index),
    }


def command_check(_: argparse.Namespace) -> int:
    counts = validate()
    print(
        "corpus ok: "
        f"{counts['sources']} sources, {counts['passages']} passages, "
        f"{counts['statements']} statements, {counts['claims']} claims, "
        f"{counts['inferences']} inferences, {counts['arguments']} arguments, "
        f"{counts['relations']} relations, {counts['results']} results, "
        f"{counts['candidates']} candidates, {counts['definitions']} definitions, "
        f"{counts['disambiguations']} disambiguations"
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
        "definitions",
        "disambiguations",
    ):
        print(f"{key + ':':16} {counts[key]}")
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


def command_frontier(args: argparse.Namespace) -> int:
    validate()
    statements = [record for _, record in load_dir("statements")]
    arguments = [record for _, record in load_dir("arguments")]
    results = [record for _, record in load_dir("results")]
    relations = [record for _, record in load_dir("relations")]
    claims = [record for _, record in load_dir("claims")]
    report = frontier_report(
        statements,
        arguments,
        results,
        relations,
        root=args.root,
        transcription=transcription_flags(results, arguments, statements),
        claims=claims,
    )
    if args.reaching_root:
        report["items"] = [item for item in report["items"] if item["path_to_root"] is not None]
        report["open_premise_count"] = len(report["items"])
        report["depth_counts"] = depth_counts(report["items"])
        on_path = {
            argument_id
            for item in report["items"]
            for argument_id in item["transitive_dependent_arguments"]
        }
        report["transcription_flags"] = [
            flag for flag in report["transcription_flags"] if flag["argument_id"] in on_path
        ]
        report["closed_via_transcription"] = [
            closure for closure in report["closed_via_transcription"] if closure["path_to_root"] is not None
        ]
    if args.json:
        print(json.dumps(report, indent=2, ensure_ascii=False))
    else:
        print(format_frontier(report))
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

# Theory definitions (#149, #160): a hypothesis whose head lies in one of these
# namespaces is a theory bundle. bind-check unfolds it exactly one step, splits
# it on `∧`, and binds every conjunct to a premise statement; the conjuncts must
# cover the argument's premises exactly. A consistency conclusion that is such a
# definition lists its commitments the same way (see scripts/BindTypes.lean).
THEORY_BUNDLE_PREFIXES = ["TruthCore.Comparison."]


def bind_tool_input(results: list[tuple[Path, dict[str, Any]]]) -> dict[str, list[str]]:
    """The modules to import and the theorems to describe, in result-id order."""
    ordered = sorted((record for _, record in results), key=lambda record: record["id"])
    return {
        "modules": sorted({record["solution_module"] for record in ordered}),
        "theorems": [record["theorem"] for record in ordered],
        "bundle_prefixes": THEORY_BUNDLE_PREFIXES,
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


# Statements without `lean_declaration` cannot be bound by head constant. Each
# such binding must be pinned here to the exact (whitespace-normalized) Lean
# type it stands for; any other undeclared binding fails bind-check, and so
# does a pin that no result uses any more.
PINNED_UNDECLARED_BINDINGS: dict[tuple[str, str, str], str] = {
    ("PLATO-TIM-28A-28C-COSMOS-CAUSE-A", "conclusion", "STMT-COSMOS-HAS-CAUSE"):
        "∃ cause, Causes cause cosmos",
    ("PLATO-TIM-28A-28C-COSMOS-CAUSE-B", "conclusion", "STMT-COSMOS-HAS-DISTINCT-CAUSE"):
        "∃ cause, cause ≠ cosmos ∧ Causes cause cosmos",
}


def normalize_type(text: str) -> str:
    return " ".join(text.split())


def bind_result(
    result: dict[str, Any],
    argument: dict[str, Any],
    statement_index: dict[str, tuple[Path, dict[str, Any]]],
    described: dict[str, Any],
    pins: dict[tuple[str, str, str], str] | None = None,
) -> dict[str, Any]:
    """Compare one result's argument record with the Lean description of its theorem.

    A binder whose type lives in `Prop` is a premise hypothesis; every other
    binder (`Type`/`Sort` parameters, predicates, individuals) is vocabulary.
    A premise or conclusion statement binds to a hypothesis or result type by
    equality of its `lean_declaration` with the type's head constant.

    A statement without `lean_declaration` cannot be bound by head constant.
    It is matched to a type whose head is not a `TruthCore` declaration (a
    logical form such as `∃ x, …` over vocabulary). That binding passes only
    when `pins` (default `PINNED_UNDECLARED_BINDINGS`) records exactly that
    Lean type for this result, role and statement; the result is then
    `pinned`. If the type's head is a `TruthCore` declaration, the statement
    should name it, and that is a mismatch.
    """
    if pins is None:
        pins = PINNED_UNDECLARED_BINDINGS

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
    hypotheses: list[dict[str, Any]] = []
    for index, binder in enumerate(binders):
        if not binder["prop"]:
            continue
        bundle = binder.get("bundle")
        if bundle is None:
            hypotheses.append(dict(binder, position=index, conjunct=None))
        elif not isinstance(bundle, list):
            problems.append(
                {"kind": "bundle-unfold-failed", "hypothesis": binder["name"], "head": binder["head"]}
            )
        else:
            # A theory bundle stands for its conjuncts; the bundle itself binds to nothing.
            for number, conjunct in enumerate(bundle):
                hypotheses.append(
                    dict(
                        conjunct,
                        name=f"{binder['name']}.{number + 1}",
                        position=index,
                        conjunct=number,
                        bundle=binder["head"],
                    )
                )

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
        entry = {
            "hypothesis": hypothesis["name"],
            "position": hypothesis["position"],
            "statement_id": match,
            "lean_declaration": hypothesis["head"],
        }
        if hypothesis.get("bundle"):
            entry["bundle"] = hypothesis["bundle"]
            entry["conjunct"] = hypothesis["conjunct"]
        premises.append(entry)
    # Second pass: statements without a declaration take logical-form hypotheses.
    for hypothesis in unmatched:
        if hypothesis.get("bundle"):
            # Bundle conjuncts never bind by logical form or pin.
            problems.append(
                {
                    "kind": "unbound-bundle-conjunct",
                    "hypothesis": hypothesis["name"],
                    "bundle": hypothesis["bundle"],
                    "head": hypothesis["head"],
                    "type": hypothesis["type"],
                }
            )
            continue
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

    commitments: list[dict[str, Any]] = []
    commitment_ids = list(argument.get("commitment_statement_ids", []))
    if not commitment_ids and outcome.get("bundle") is not None:
        # A theory-definition conclusion is a consistency claim; its commitments
        # must be recorded so that every conjunct is checked.
        problems.append(
            {"kind": "theory-conclusion-without-commitments", "head": outcome.get("head"), "type": outcome["type"]}
        )
    if commitment_ids:
        bundle = outcome.get("bundle")
        if not isinstance(bundle, list):
            problems.append(
                {"kind": "commitments-without-bundle", "head": outcome.get("head"), "type": outcome["type"]}
            )
        else:
            for number, item in enumerate(bundle):
                match = next(
                    (sid for sid in commitment_ids if declaration(sid) is not None and declaration(sid) == item["head"]),
                    None,
                )
                if match is None:
                    problems.append(
                        {"kind": "unbound-commitment", "position": number, "head": item["head"], "type": item["type"]}
                    )
                    continue
                commitment_ids.remove(match)
                commitments.append({"position": number, "statement_id": match, "lean_declaration": item["head"]})
            for statement_id in commitment_ids:
                problems.append(
                    {"kind": "missing-commitment", "statement_id": statement_id, "lean_declaration": declaration(statement_id)}
                )

    for item in undecidable:
        key = (result["id"], item["role"], item["statement_id"])
        item["pin"] = list(key)
        pinned = pins.get(key)
        if pinned is None or normalize_type(pinned) != normalize_type(item["type"]):
            problems.append(
                {
                    "kind": "undeclared-binding",
                    "role": item["role"],
                    "statement_id": item["statement_id"],
                    "type": item["type"],
                    "pinned_type": pinned,
                }
            )

    if problems:
        status = "mismatch"
    elif undecidable:
        status = "pinned"
    else:
        status = "bound"
    premises.sort(key=lambda entry: (entry["position"], entry.get("conjunct") or 0))
    return {
        "id": result["id"],
        "theorem": result["theorem"],
        "status": status,
        "premises": [dict(sorted(entry.items())) for entry in premises],
        "conclusion": dict(sorted(conclusion.items())),
        "commitments": commitments,
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
    used = {tuple(item["pin"]) for entry in entries for item in entry["undecidable"]}
    stale = sorted(list(key) for key in PINNED_UNDECLARED_BINDINGS if key not in used)
    summary = Counter(entry["status"] for entry in entries)
    return {
        "summary": {status: summary.get(status, 0) for status in ("bound", "pinned", "mismatch")},
        "stale_pins": stale,
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
            if entry["status"] == "pinned":
                for item in entry["undecidable"]:
                    print(
                        f"pinned: {entry['id']}: {item['role']} {item['statement_id']} "
                        f"has no lean_declaration; Lean type is `{item['type']}`"
                    )
            for problem in entry["problems"]:
                print(f"mismatch: {entry['id']}: {json.dumps(problem, ensure_ascii=False, sort_keys=True)}")
        summary = report["summary"]
        print(
            f"bind-check: {summary['bound']} bound, {summary['pinned']} pinned, "
            f"{summary['mismatch']} mismatch"
        )
        for key in report["stale_pins"]:
            print(f"stale pin: {key} is not used by any result; remove it from PINNED_UNDECLARED_BINDINGS")
    return 1 if report["summary"]["mismatch"] or report["stale_pins"] else 0


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
    frontier = sub.add_parser(
        "frontier",
        help="list open premises: not verified, not self-evident, alternatives not all refuted",
    )
    frontier.add_argument("--json", action="store_true", help="print the report as JSON")
    frontier.add_argument(
        "--root",
        default=DEFAULT_FRONTIER_ROOT,
        help=f"statement whose dependency path is shown (default {DEFAULT_FRONTIER_ROOT})",
    )
    frontier.add_argument(
        "--reaching-root",
        action="store_true",
        help="list only open premises from which the root is reached",
    )
    frontier.set_defaults(func=command_frontier)
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
    return main_with(None)


def main_with(argv: list[str] | None) -> int:
    args = parser().parse_args(argv)
    try:
        return args.func(args)
    except CorpusError as exc:
        print(f"corpus error: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
