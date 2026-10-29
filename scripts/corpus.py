#!/usr/bin/env python3
"""Small, dependency-free corpus queue/validation tool for truth-core."""

from __future__ import annotations

import argparse
import json
import re
import sys
from collections import Counter
from pathlib import Path
from typing import Any, Callable, Iterable

from source_evidence import BIBLIOGRAPHIC_WITNESS, SourceEvidenceError, validate_bindings
from premise_dossiers import dossier_index, format_dossier, validate_attempt
from finite_models import validate_model, model_report, verify_models
from configurations import validate_case, configuration_report, verify_case, verify_compositions
from territory import format_territory, territory_report

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


# Order-free lists that many PRs append to. Keeping them sorted makes
# concurrent additions land at different lines instead of all at the end.
# `corpus.py sort-lists` sorts them in place.
SORTED_LIST_FIELDS: dict[str, tuple[str, ...]] = {
    "sources": ("edition_urns",),
}


def unsorted_lists() -> list[tuple[Path, str, str]]:
    """(path, field, raw text) for every record whose order-free list is not sorted."""
    found = []
    for directory, fields in SORTED_LIST_FIELDS.items():
        for path in sorted((CORPUS / directory).glob("*.json")):
            raw = path.read_text(encoding="utf-8")
            record = json.loads(raw)
            for field in fields:
                value = record.get(field)
                if isinstance(value, list) and value != sorted(value):
                    found.append((path, field, raw))
    return found


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


# The only axioms a Comparator config may permit, and only when the Solution
# transitively imports Mathlib (AGENTS.md invariant 14, docs/axiom-policy.md).
# Results that do not use Mathlib stay zero-axiom.
MATHLIB_PERMITTED_AXIOMS = ("propext", "Classical.choice", "Quot.sound")
LEAN_IMPORT_RE = re.compile(r"^(?:public\s+)?import\s+(\S+)", re.MULTILINE)


def imports_mathlib(module: str) -> bool:
    """Whether a TruthCore module imports Mathlib, directly or through other
    TruthCore modules."""
    seen: set[str] = set()
    pending = [module]
    while pending:
        current = pending.pop()
        if current in seen:
            continue
        seen.add(current)
        if current == "Mathlib" or current.startswith("Mathlib."):
            return True
        path = module_path(current)
        if not current.startswith("TruthCore") or not path.is_file():
            continue
        pending.extend(LEAN_IMPORT_RE.findall(path.read_text(encoding="utf-8")))
    return False


def permitted_axioms_error(config: dict[str, Any]) -> str | None:
    """Why a Comparator config's `permitted_axioms` violates the axiom policy,
    or None when it complies."""
    axioms = config.get("permitted_axioms")
    if axioms == []:
        return None
    if not isinstance(axioms, list) or sorted(axioms) != sorted(MATHLIB_PERMITTED_AXIOMS):
        return (
            "permitted_axioms must be [] or exactly "
            f"{list(MATHLIB_PERMITTED_AXIOMS)} (docs/axiom-policy.md)"
        )
    if not imports_mathlib(config.get("solution_module", "")):
        return (
            "only a Solution that imports Mathlib may permit "
            f"{list(MATHLIB_PERMITTED_AXIOMS)}; results without Mathlib stay zero-axiom"
        )
    return None


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
# Metadata only: never source support or premise closure.
SCHEMA_INSTANCE_PREDICATE = "instance_of_schema"
# Designated route (argument → statement; owner decision on #143, 2026-10-24):
# when a statement has root_route relations, `frontier` walks up into it only
# through the designated arguments, so premises of other arguments for the same
# conclusion do not reach the root through it.
ROOT_ROUTE_PREDICATE = "root_route"
DEFAULT_FRONTIER_ROOT = "STMT-CATHOLICISM-TRUE"
# Stage conclusions of the root skeleton (#156; CATHOLICISM-SKELETON, docs/catholic-case.md).
# Views group statements by the stage conclusions that rest on them.
STAGE_CONCLUSIONS = (
    (1, "STMT-GOD-EXISTS"),
    (2, "STMT-GOD-HAS-CLASSICAL-DIVINE-ATTRIBUTES"),
    (3, "STMT-REVELATION-POSSIBLE-AND-RECOGNIZABLE"),
    (4, "STMT-JESUS-CLAIMED-DIVINE-AUTHORITY-AND-ROSE"),
    (5, "STMT-CHRIST-FOUNDED-VISIBLE-CHURCH"),
    (6, "STMT-CHRISTS-CHURCH-IS-THE-CATHOLIC-CHURCH"),
)
# Depth of an open premise (#143, 2026-10-24): "bare" when no claim states it
# and no `supports` relation points to it; otherwise "sourced" (sourced but not
# yet defended). The aim is to drive bare premises to zero, then defend the rest.
FRONTIER_BARE = "bare"
FRONTIER_SOURCED = "sourced"


# Floor bases (#500; #497, "The floor: criteria, not owner approval"). A
# self_evident marking names the written criterion it meets. `frontier_report`
# recomputes from the current relations, claims and results whether that
# criterion holds; a marking whose criterion fails closes nothing, and
# `corpus.py check` warns about it. `logical` is no basis: such a premise is
# proved instead and closes as a result.
FLOOR_RETORSION = "retorsion"
FLOOR_COMMON_GROUND = "common_ground"
FLOOR_OBSERVATION = "observation"
FLOOR_BASES = {FLOOR_RETORSION, FLOOR_COMMON_GROUND, FLOOR_OBSERVATION}
# The documented legacy default: a marking made before #500 without a basis.
# Only the statements listed here may omit the basis; they close as recorded.
FLOOR_LEGACY = "legacy"
LEGACY_FLOOR_STATEMENTS = {"STMT-EXCLUDED-MIDDLE"}
# The floor is a last resort (#378, point 3: people disagree about what is
# self-evident). Every marking except common_ground (whose recorded rivals'
# agreement is its disagreement record) records the known disagreement:
# `disagreement` is either this literal or an object listing the recorded
# rivals and/or claims that deny the statement is self-evident.
DISAGREEMENT_NONE = "none recorded"


def validate_disagreement(where: Path, marking: dict[str, Any], basis: str, claim_ids: set[str],
                          statement_ids: set[str] | None) -> None:
    disagreement = marking.get("disagreement")
    if disagreement is None:
        if basis == FLOOR_COMMON_GROUND:
            return
        raise CorpusError(
            f"{where}: self_evident needs a disagreement record (#378): "
            f'"{DISAGREEMENT_NONE}" or {{"rival_statement_ids": [...], "claim_ids": [...]}}'
        )
    if disagreement == DISAGREEMENT_NONE:
        return
    if not isinstance(disagreement, dict) or set(disagreement) - {"rival_statement_ids", "claim_ids", "note"}:
        raise CorpusError(f"{where}: self_evident disagreement must be \"{DISAGREEMENT_NONE}\" or an object")
    rivals = disagreement.get("rival_statement_ids", [])
    claims = disagreement.get("claim_ids", [])
    for field, values, known in (("rival_statement_ids", rivals, statement_ids), ("claim_ids", claims, claim_ids)):
        if not isinstance(values, list) or any(not isinstance(value, str) for value in values):
            raise CorpusError(f"{where}: self_evident disagreement {field} must be a list of ids")
        unknown = [value for value in values if known is not None and value not in known]
        if unknown:
            raise CorpusError(f"{where}: self_evident disagreement {field} unknown: {', '.join(unknown)}")
    if not rivals and not claims:
        raise CorpusError(f"{where}: an object disagreement lists rivals or claims; otherwise use \"{DISAGREEMENT_NONE}\"")


def validate_self_evident(
    path: Path,
    statement: dict[str, Any],
    claim_ids: set[str],
    result_ids: set[str],
    statement_ids: set[str] | None = None,
) -> None:
    """Shape of a self_evident marking and of its basis-specific evidence.
    Whether the criterion currently holds is computed by `frontier_report`."""
    marking = statement.get("self_evident")
    if marking is None:
        return
    where = path.relative_to(ROOT)
    if not isinstance(marking, dict):
        raise CorpusError(f"{where}: self_evident must be an object with justification_ids")
    justification = require_string_list(marking, "justification_ids", path, allow_empty=False)
    for justification_id in justification:
        if justification_id not in claim_ids and justification_id not in result_ids:
            raise CorpusError(
                f"{where}: self_evident justification {justification_id} "
                "is neither a claim id nor a result id"
            )
    basis = marking.get("basis")
    if basis is None:
        if statement.get("id") not in LEGACY_FLOOR_STATEMENTS:
            raise CorpusError(
                f"{where}: self_evident needs a basis ({', '.join(sorted(FLOOR_BASES))}); "
                "only the documented legacy markings may omit it"
            )
        validate_disagreement(where, marking, FLOOR_LEGACY, claim_ids, statement_ids)
        return
    if basis not in FLOOR_BASES:
        raise CorpusError(f"{where}: self_evident basis must be one of {', '.join(sorted(FLOOR_BASES))}")
    validate_disagreement(where, marking, basis, claim_ids, statement_ids)

    def known_statement(field: str, value: Any) -> None:
        if not isinstance(value, str) or not value:
            raise CorpusError(f"{where}: self_evident {field} must be a statement id")
        if statement_ids is not None and value not in statement_ids:
            raise CorpusError(f"{where}: self_evident {field} {value} is not a known statement")

    if basis == FLOOR_RETORSION:
        if any(justification_id not in result_ids for justification_id in justification):
            raise CorpusError(f"{where}: a retorsion basis is justified by results only")
        known_statement("denial_statement_id", marking.get("denial_statement_id"))
    elif basis == FLOOR_COMMON_GROUND:
        known_statement("question_statement_id", marking.get("question_statement_id"))
        positions = marking.get("positions")
        if not isinstance(positions, list) or not positions:
            raise CorpusError(f"{where}: a common_ground basis needs a non-empty positions list")
        cited: set[str] = set()
        for position in positions:
            if not isinstance(position, dict):
                raise CorpusError(f"{where}: each common_ground position is an object")
            known_statement("position statement_id", position.get("statement_id"))
            cited.update(require_string_list(position, "claim_ids", path, allow_empty=False))
        if cited != set(justification):
            raise CorpusError(
                f"{where}: common_ground justification_ids must be exactly the claims its positions cite"
            )
    else:
        if not any(justification_id in claim_ids for justification_id in justification):
            raise CorpusError(f"{where}: an observation basis needs a sourced claim among its justifications")
        if "sceptical_rival_ids" in marking:
            for rival in require_string_list(marking, "sceptical_rival_ids", path, allow_empty=True):
                known_statement("sceptical_rival_ids entry", rival)


def validate_premise_program_relation(path: Path, relation: dict[str, Any]) -> None:
    predicate = relation["predicate"]
    expected = {
        ALTERNATIVE_PREDICATE: ({"statement"}, "statement"),
        REFUTES_PREDICATE: ({"argument"}, "statement"),
        ATTACKS_PREDICATE: ({"statement", "claim", "argument"}, "statement"),
        SUPPORTS_PREDICATE: ({"claim"}, "statement"),
        SCHEMA_INSTANCE_PREDICATE: ({"statement"}, "statement"),
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


def validate_schema_registration(
    path: Path,
    relation: dict[str, Any],
    results: dict[str, dict[str, Any]],
    configs: dict[str, dict[str, Any]],
) -> None:
    """Require named Comparator obligations; metadata is not verification."""
    if relation["predicate"] != SCHEMA_INSTANCE_PREDICATE:
        return
    require(relation, ["verification_result_id", "instance_theorem", "schema_theorem", "note"], path)
    if not isinstance(relation["note"], str) or not relation["note"].strip():
        raise CorpusError(f"{path.relative_to(ROOT)}: schema registration note must be nonempty text")
    result_id = relation["verification_result_id"]
    if not isinstance(result_id, str) or result_id not in results:
        raise CorpusError(f"{path.relative_to(ROOT)}: unknown verification_result_id {result_id}")
    for field in ("instance_theorem", "schema_theorem"):
        theorem = relation[field]
        if not isinstance(theorem, str) or theorem not in configs[result_id].get("theorem_names", []):
            raise CorpusError(
                f"{path.relative_to(ROOT)}: {field} must name an obligation in "
                f"{result_id}'s Comparator config"
            )


def schema_binding_records(
    relations: list[dict[str, Any]], results: dict[str, dict[str, Any]],
) -> list[tuple[dict[str, Any], dict[str, Any]]]:
    """Reuse bind-check for each registered theorem's exact statement head.

    These synthetic binding requests are not corpus arguments or frontier
    proofs. Philosophical conditions belong inside the named conditional
    statement; extra proof hypotheses must not pass as proved instances.
    """
    bindings = []
    for relation in sorted(relations, key=lambda record: record["id"]):
        if relation["predicate"] != SCHEMA_INSTANCE_PREDICATE:
            continue
        result = results[relation["verification_result_id"]]
        for side, theorem_field, statement_field in (
            ("instance", "instance_theorem", "subject_id"),
            ("schema", "schema_theorem", "object_id"),
        ):
            binding = {
                "id": f"{relation['id']}:{side}",
                "solution_module": result["solution_module"],
                "theorem": relation[theorem_field],
            }
            argument = {"premise_statement_ids": [], "conclusion_statement_id": relation[statement_field]}
            bindings.append((binding, argument))
    return bindings


# Transcription kinds (#391). A result record may declare that it is a
# transcription (AGENTS.md invariant 16) in the structured `transcription`
# field; prose in `description` is commentary, not the flag.
TRANSCRIPTION_OPAQUE_ATOMS = "opaque_atoms"
TRANSCRIPTION_SINGLE_APPLICATION = "single_application"
TRANSCRIPTION_ASSEMBLY = "assembly"
TRANSCRIPTION_INSTANTIATION = "instantiation"
TRANSCRIPTION_KINDS = {
    TRANSCRIPTION_OPAQUE_ATOMS: "every proposition the theorem relates is an unconstrained `Prop` parameter",
    TRANSCRIPTION_SINGLE_APPLICATION: "the proof applies one premise whose consequent is the conclusion",
    TRANSCRIPTION_ASSEMBLY: "the proof only pairs or destructures hypotheses (conjunction or tuple assembly)",
    TRANSCRIPTION_INSTANTIATION: "the proof only instantiates a general premise or lemma at the case",
}
# A description that opens with one of these labels must carry the field.
TRANSCRIPTION_LABEL_RE = re.compile(r"^(?:Opaque-atom |Near-|Logical )?[Tt]ranscription\b")


def validate_result_transcription(label: Any, result: dict[str, Any]) -> None:
    """The structured `transcription` field (#391): one of TRANSCRIPTION_KINDS,
    and required when the description opens with a transcription label."""
    declared = result.get("transcription")
    if declared is not None and declared not in TRANSCRIPTION_KINDS:
        raise CorpusError(
            f"{label}: transcription must be one of {', '.join(sorted(TRANSCRIPTION_KINDS))}"
        )
    if declared is None and TRANSCRIPTION_LABEL_RE.match(result.get("description", "")):
        raise CorpusError(
            f"{label}: description labels the result a transcription; "
            "declare it in the structured transcription field (#391)"
        )


def root_routes(
    root: str | None,
    statement_by_id: dict[str, dict[str, Any]],
    argument_by_id: dict[str, dict[str, Any]],
    results: list[dict[str, Any]],
    transcription_results: set[str],
    closed: set[str],
    established: set[str],
    sourced: Any,
    designated: set[str],
) -> dict[str, Any]:
    """Official per-route open-premise count (#391, owner decision 2026-10-26,
    corrected the same day).

    Each statement is assigned a set of open leaves; its cost is that set's
    size. An established statement has none. A statement may stand as a
    single open leaf (cost 1) only when it is a genuine premise: a claim
    states it or supports it (sourced), or no argument concludes it (bare
    leaf). Any other statement, an intermediate conclusion, is expanded: its
    leaves are the union of its premises' leaves under the verified
    non-transcription proof whose union is smallest. A transcription never
    expands a statement (rule (d): it only carries closure from closed
    premises, which makes its conclusion established). An intermediate
    conclusion with no usable proof (only unverified or transcription
    arguments, or a cycle with no grounded proof) falls back to a leaf.

    The minimum over proofs is taken per statement and the unions are then
    formed upward, so overlaps between premises are counted once but the
    choice is greedy: an exact minimum set cover over the whole graph is not
    attempted. Iteration runs to a fixpoint in which a statement's set only
    changes to a strictly smaller one, so it terminates and is deterministic
    (proofs by argument ID). A sourced premise always stays a single leaf or
    becomes established, so adding a derivation under a sourced premise never
    raises a route's cost.

    A route is an argument concluding the root; its cost is the size of the
    union of its distinct premises' leaf sets. The cheapest verified route is
    marked."""
    if root is None:
        return {"root": root, "cheapest_argument_id": None, "routes": []}
    results_by_argument: dict[str, list[str]] = {}
    for result in results:
        results_by_argument.setdefault(result["argument_id"], []).append(result["id"])
    statement_ids = set(statement_by_id)
    concluded: set[str] = set()
    for argument in argument_by_id.values():
        statement_ids.update(argument["premise_statement_ids"])
        statement_ids.add(argument["conclusion_statement_id"])
        concluded.add(argument["conclusion_statement_id"])
    leaves: dict[str, frozenset[str] | None] = {}
    for statement_id in statement_ids:
        if statement_id in established:
            leaves[statement_id] = frozenset()
        elif sourced(statement_id) or statement_id not in concluded:
            leaves[statement_id] = frozenset({statement_id})
        else:
            leaves[statement_id] = None
    proofs = sorted(
        (argument_id, argument_by_id[argument_id])
        for argument_id, result_ids in results_by_argument.items()
        if argument_id in argument_by_id
        and any(result_id not in transcription_results for result_id in result_ids)
    )
    changed = True
    while changed:
        changed = False
        for _, argument in proofs:
            conclusion = argument["conclusion_statement_id"]
            premise_sets = [leaves[premise] for premise in set(argument["premise_statement_ids"])]
            if any(premise_set is None for premise_set in premise_sets):
                continue
            candidate = frozenset().union(*premise_sets)
            current = leaves[conclusion]
            if current is None or len(candidate) < len(current):
                leaves[conclusion] = candidate
                changed = True
    for statement_id, value in leaves.items():
        if value is None:
            leaves[statement_id] = frozenset({statement_id})

    entries: list[dict[str, Any]] = []
    for argument_id in sorted(argument_by_id):
        argument = argument_by_id[argument_id]
        if argument["conclusion_statement_id"] != root:
            continue
        premises = sorted(set(argument["premise_statement_ids"]))
        open_premises = sorted(frozenset().union(*(leaves[premise] for premise in premises)))
        result_ids = results_by_argument.get(argument_id, [])
        entries.append(
            {
                "argument_id": argument_id,
                "cost": len(open_premises),
                "premise_count": len(premises),
                "verified": bool(result_ids),
                "transcription": bool(result_ids)
                and all(result_id in transcription_results for result_id in result_ids),
                "designated": argument_id in designated,
                "cheapest": False,
                "open_premise_statement_ids": open_premises,
                "proved_unestablished_statement_ids": [
                    premise for premise in open_premises if premise in closed
                ],
            }
        )
    verified = [entry for entry in entries if entry["verified"]]
    cheapest = min(verified, key=lambda entry: (entry["cost"], entry["argument_id"])) if verified else None
    if cheapest is not None:
        cheapest["cheapest"] = True
    entries.sort(key=lambda entry: (not entry["verified"], entry["cost"], entry["argument_id"]))
    return {
        "root": root,
        "cheapest_argument_id": cheapest["argument_id"] if cheapest else None,
        "routes": entries,
    }


def transcription_kinds(
    results: list[dict[str, Any]],
    transcription: list[dict[str, Any]] | None,
) -> dict[str, dict[str, Any]]:
    """Results that are transcriptions (invariant 16), with their kind.

    A result is a transcription when its record declares one in the structured
    `transcription` field (#391), or when the Lean text heuristics find that
    its proof is a single application of one hypothesis or only assembles
    hypotheses into a tuple (`⟨hClaims, hRose⟩`, #391). A declared kind wins
    over a heuristic one. The opaque-atom heuristic only warns: it never makes
    a result a transcription by itself."""
    kinds: dict[str, dict[str, Any]] = {}
    for flag in transcription or []:
        if flag.get("single_application_of"):
            kinds[flag["result_id"]] = {"kind": TRANSCRIPTION_SINGLE_APPLICATION, "declared": False}
        elif flag.get("assembly_of"):
            kinds[flag["result_id"]] = {"kind": TRANSCRIPTION_ASSEMBLY, "declared": False}
    for result in results:
        declared = result.get("transcription")
        if declared:
            kinds[result["id"]] = {"kind": declared, "declared": True}
    return dict(sorted(kinds.items()))


def frontier_report(
    statements: list[dict[str, Any]],
    arguments: list[dict[str, Any]],
    results: list[dict[str, Any]],
    relations: list[dict[str, Any]],
    root: str | None = DEFAULT_FRONTIER_ROOT,
    transcription: list[dict[str, Any]] | None = None,
    claims: list[dict[str, Any]] | None = None,
    inferences: list[dict[str, Any]] | None = None,
) -> dict[str, Any]:
    """Open premises: used as an argument premise and not closed. A statement
    is closed when it is (a) the conclusion of a verified result that is not a
    transcription (invariant 16), (b) marked self_evident, (c) refuted in every
    one of its recorded alternatives (at least one alternative recorded), or
    (d) the conclusion of a transcription result all of whose argument premises
    are closed (#143, 2026-10-24). A `refutes` relation counts for (c) only
    when its argument has a verified result and all of that argument's
    premises are closed (#391). Rules (c) and (d) are applied jointly to a
    fixpoint.

    Each open premise also gets a depth (#143, 2026-10-24): "bare" when no
    claim states it and no `supports` relation points to it, otherwise
    "sourced" (sourced but undefended)."""
    statement_by_id = {statement["id"]: statement for statement in statements}
    argument_by_id = {argument["id"]: argument for argument in arguments}
    verified_arguments = {result["argument_id"] for result in results}
    # Invariant 16: a transcription closes no frontier node. A conclusion is
    # closed by rule (a) only by a verified result that is not a transcription:
    # neither declared one in its record nor found by the Lean heuristics.
    kinds = transcription_kinds(results, transcription)
    transcription_results = set(kinds)
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
    refutations: list[dict[str, Any]] = []
    objections: dict[str, set[str]] = {}
    support: dict[str, set[str]] = {}
    routes: dict[str, set[str]] = {}
    for relation in relations:
        predicate = relation.get("predicate")
        if predicate == ALTERNATIVE_PREDICATE:
            alternatives.setdefault(relation["object_id"], set()).add(relation["subject_id"])
        elif predicate == REFUTES_PREDICATE:
            refutations.append(relation)
        elif predicate == ATTACKS_PREDICATE:
            objections.setdefault(relation["object_id"], set()).add(
                f"{relation['subject_kind']}:{relation['subject_id']}"
            )
        elif predicate == SUPPORTS_PREDICATE:
            support.setdefault(relation["object_id"], set()).add(relation["subject_id"])
        elif predicate == ROOT_ROUTE_PREDICATE:
            routes.setdefault(relation["object_id"], set()).add(relation["subject_id"])
    refutations.sort(key=lambda relation: relation["id"])

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

    closed = set(verified_conclusions)
    refuted: set[str] = set()

    # Floor markings (#500): rule (b) closes a self_evident statement only
    # while its basis criterion holds, recomputed here from the current
    # records. The criteria only grow with `closed` and `refuted`, so they are
    # evaluated inside the fixpoint below.
    claim_statement = {claim["id"]: claim["statement_id"] for claim in claims or []}
    result_by_id = {result["id"]: result for result in results}
    refuting_arguments: dict[str, set[str]] = {}
    for relation in refutations:
        refuting_arguments.setdefault(relation["object_id"], set()).add(relation["subject_id"])
    floor_markings = {
        statement_id: statement["self_evident"]
        for statement_id, statement in statement_by_id.items()
        if statement.get("self_evident") is not None
    }

    def floor_reasons(statement_id: str) -> list[str]:
        """Why the marking's criterion does not hold now; empty when it does."""
        marking = floor_markings[statement_id]
        basis = marking.get("basis") or FLOOR_LEGACY
        rivals = sorted(alternatives.get(statement_id, ()))
        justification = marking.get("justification_ids", [])
        # #378: the recorded disagreement must cover every current rival, so
        # a newly recorded rival is not hidden behind a stale record.
        disagreement = marking.get("disagreement")
        if disagreement is not None and basis != FLOOR_COMMON_GROUND:
            listed = set(disagreement.get("rival_statement_ids", [])) if isinstance(disagreement, dict) else set()
            unlisted = [rival for rival in rivals if rival not in listed]
            if unlisted:
                return ["disagreement record omits recorded rivals: " + ", ".join(unlisted)]
        if basis == FLOOR_LEGACY:
            return []
        if basis == FLOOR_RETORSION:
            denial = marking.get("denial_statement_id")
            if denial not in alternatives.get(statement_id, ()):
                return [f"denial {denial} is not recorded as alternative_to {statement_id}"]
            reasons: list[str] = []
            for result_id in justification:
                result = result_by_id.get(result_id)
                argument = argument_by_id.get(result["argument_id"]) if result else None
                if argument is None:
                    reasons.append(f"{result_id} has no argument")
                elif result_id in transcription_results:
                    reasons.append(f"{result_id} is a transcription")
                elif argument["id"] not in refuting_arguments.get(denial, ()):
                    reasons.append(f"{argument['id']} has no refutes relation to {denial}")
                else:
                    open_premises = sorted(
                        {premise for premise in argument["premise_statement_ids"] if premise not in closed}
                    )
                    if not open_premises:
                        return []
                    reasons.append(f"{result_id} rests on open premises {', '.join(open_premises)}")
            return reasons
        if basis == FLOOR_COMMON_GROUND:
            if rivals:
                return [f"recorded rivals deny it: {', '.join(rivals)}"]
            question = marking.get("question_statement_id")
            question_rivals = sorted(alternatives.get(question, ()))
            if not question_rivals:
                return [f"no rival position recorded on {question}"]
            committed: dict[str, list[str]] = {}
            for position in marking.get("positions", []):
                stating = [
                    claim_id
                    for claim_id in position.get("claim_ids", [])
                    if claim_statement.get(claim_id) == statement_id
                ]
                committed.setdefault(position.get("statement_id"), []).extend(stating)
            missing = [position for position in [question, *question_rivals] if not committed.get(position)]
            if missing:
                return ["no proponent claim stating it for position " + ", ".join(missing)]
            return []
        # observation
        reasons = []
        if not any(claim_statement.get(claim_id) == statement_id for claim_id in justification):
            reasons.append("no justification claim states it")
        sceptical = set(marking.get("sceptical_rival_ids", []))
        not_sceptical = [rival for rival in rivals if rival not in sceptical]
        if not_sceptical:
            reasons.append("rivals not recorded as global sceptical positions: " + ", ".join(not_sceptical))
        unrefuted = [rival for rival in rivals if rival in sceptical and rival not in refuted]
        if unrefuted:
            reasons.append("sceptical rivals not refuted: " + ", ".join(unrefuted))
        return reasons

    def refutation_counts(relation: dict[str, Any]) -> bool:
        argument = argument_by_id.get(relation["subject_id"])
        return (
            argument is not None
            and relation["subject_id"] in verified_arguments
            and all(premise in closed for premise in argument["premise_statement_ids"])
        )

    def defended(statement_id: str) -> bool:
        recorded = alternatives.get(statement_id, ())
        return bool(recorded) and all(alternative in refuted for alternative in recorded)

    # Rules (c) and (d), jointly to a fixpoint. A refutation counts only from a
    # premise-free argument or one whose premises are all closed (#391), and a
    # transcription carries closure from its premises to its conclusion
    # (#143, 2026-10-24). Each pass visits refutations by relation ID and
    # transcription results by result ID, so the recorded result for a
    # conclusion is deterministic.
    transcription_steps = sorted(
        (result["id"], argument_by_id[result["argument_id"]])
        for result in results
        if result["id"] in transcription_results and result["argument_id"] in argument_by_id
    )
    closed_via_transcription: dict[str, dict[str, Any]] = {}
    changed = True
    while changed:
        changed = False
        for statement_id in sorted(floor_markings):
            if statement_id not in closed and not floor_reasons(statement_id):
                closed.add(statement_id)
                changed = True
        for relation in refutations:
            if relation["object_id"] not in refuted and refutation_counts(relation):
                refuted.add(relation["object_id"])
                changed = True
        for statement_id in alternatives:
            if statement_id not in closed and defended(statement_id):
                closed.add(statement_id)
                changed = True
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

    refutation_report = []
    for relation in refutations:
        argument = argument_by_id.get(relation["subject_id"])
        premises = sorted(set(argument["premise_statement_ids"])) if argument else []
        refutation_report.append(
            {
                "relation_id": relation["id"],
                "argument_id": relation["subject_id"],
                "statement_id": relation["object_id"],
                "verified": relation["subject_id"] in verified_arguments,
                "open_premise_statement_ids": [premise for premise in premises if premise not in closed],
                "counted": refutation_counts(relation),
            }
        )

    # Why each closed statement is closed, for views such as the explorer's
    # state page (#200). The first matching rule wins, in the order (a)-(d).
    floor_report = []
    for statement_id in sorted(floor_markings):
        marking = floor_markings[statement_id]
        reasons = floor_reasons(statement_id)
        floor_report.append(
            {
                "statement_id": statement_id,
                "basis": marking.get("basis") or FLOOR_LEGACY,
                "met": not reasons,
                "reasons": reasons,
                "justification_ids": sorted(marking.get("justification_ids", [])),
                "disagreement": marking.get("disagreement"),
            }
        )
    floor_met = {entry["statement_id"] for entry in floor_report if entry["met"]}

    closed_statements: dict[str, str] = {}
    for statement_id in sorted(closed):
        if statement_id in verified_conclusions:
            closed_statements[statement_id] = "proved"
        elif statement_id in floor_met:
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
        if statement_id in floor_met or defended(statement_id)
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
    # Claims resting on a bibliographic span: cited by page, not byte-verified (#378).
    bibliographic_claims = {
        claim["id"] for claim in claims or [] if claim.get("witness") == BIBLIOGRAPHIC_WITNESS
    }

    route_report = root_routes(
        root,
        statement_by_id,
        argument_by_id,
        results,
        transcription_results,
        closed,
        established,
        lambda statement_id: bool(stating_claims.get(statement_id) or support.get(statement_id)),
        routes.get(root or "", set()),
    )
    # The root is closed only relative to the floor (#500): list each met
    # floor premise that reaches it with its basis.
    for entry in floor_report:
        entry["reaches_root"] = entry["statement_id"] == root or upward(entry["statement_id"])[2] is not None
    route_report["floor_bases"] = [
        {"statement_id": entry["statement_id"], "basis": entry["basis"]}
        for entry in floor_report
        if entry["met"] and entry["reaches_root"]
    ]

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
                "bibliographic_claims": sorted(
                    bibliographic_claims.intersection(
                        stating_claims.get(statement_id, set()) | support.get(statement_id, set())
                    )
                ),
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
    floor_by_id = {entry["statement_id"]: entry for entry in floor_report}
    for item in items:
        item["transcription_premise_of"] = sorted(goal_premise_arguments.get(item["statement_id"], []))
        if item["statement_id"] in floor_by_id:
            entry = floor_by_id[item["statement_id"]]
            item["floor_unmet"] = {"basis": entry["basis"], "reasons": entry["reasons"]}
    # Every statement whose `upward` walk reaches the root: the inverse walk from
    # the root through argument conclusions to their premises, entering a routed
    # conclusion only through its designated arguments (root_route).
    reaching_root: set[str] = set()
    if root is not None and root in statement_by_id:
        concluding: dict[str, list[str]] = {}
        for argument in arguments:
            concluding.setdefault(argument["conclusion_statement_id"], []).append(argument["id"])
        reaching_root.add(root)
        pending = [root]
        while pending:
            conclusion = pending.pop()
            for argument_id in concluding.get(conclusion, ()):
                if conclusion in routes and argument_id not in routes[conclusion]:
                    continue
                for premise in argument_by_id[argument_id]["premise_statement_ids"]:
                    if premise not in reaching_root:
                        reaching_root.add(premise)
                        pending.append(premise)
    closures: list[dict[str, Any]] = []
    for statement_id in sorted(closed_via_transcription):
        _, _, path = upward(statement_id)
        closures.append({**closed_via_transcription[statement_id], "path_to_root": path})
    view = statement_view(
        statement_by_id,
        arguments,
        results,
        relations,
        inferences or [],
        root,
        transcription_results,
        floor_met,
        {statement_id for statement_id in statement_by_id if defended(statement_id)},
        {item["statement_id"] for item in items},
        upward,
    )
    return {
        "root": root,
        "root_known": root is not None and root in statement_by_id,
        "transcription_flags": transcription or [],
        "transcription_results": kinds,
        "closed_via_transcription": closures,
        "refutations": refutation_report,
        "refuted_statements": sorted(refuted),
        "routes": route_report,
        "closed_statements": closed_statements,
        "floor": floor_report,
        "established_statements": sorted(established),
        "reaching_root_statements": sorted(reaching_root),
        "alternatives_recorded": bool(alternatives),
        "open_premise_count": len(items),
        "depth_counts": depth_counts(items),
        "items": items,
        **view,
    }


def statement_view(
    statement_by_id: dict[str, dict[str, Any]],
    arguments: list[dict[str, Any]],
    results: list[dict[str, Any]],
    relations: list[dict[str, Any]],
    inferences: list[dict[str, Any]],
    root: str | None,
    transcription_results: set[str],
    floor_met: set[str],
    defended: set[str],
    open_premises: set[str],
    upward: Callable[[str], tuple[list[str], list[str], list[str] | None]],
) -> dict[str, Any]:
    """Per-statement projections for views such as the explorer (#507), so no
    view recomputes them. `statement_statuses` gives one display status per
    statement, the first that applies: "proved" or "transcription" (conclusion
    of a verified result; "transcription" when every such result is one),
    "self-evident" (a floor marking whose basis criterion holds now, #500),
    "defended" (every recorded alternative refuted), "alternative" or
    "objection" (subject of an alternative_to or a statement attacks
    relation), "open" (an open premise), "derived" (output of an inference
    some argument uses), otherwise "source-only". A status adds no closure
    rule: closure is `closed_statements`."""
    argument_by_id = {argument["id"]: argument for argument in arguments}
    verifying: dict[str, list[str]] = {}
    for result in results:
        argument = argument_by_id.get(result["argument_id"])
        if argument is not None:
            verifying.setdefault(argument["conclusion_statement_id"], []).append(result["id"])
    alternative_subjects = {
        relation["subject_id"] for relation in relations if relation.get("predicate") == ALTERNATIVE_PREDICATE
    }
    objection_subjects = {
        relation["subject_id"]
        for relation in relations
        if relation.get("predicate") == ATTACKS_PREDICATE and relation.get("subject_kind") == "statement"
    }
    used_inferences = {inference_id for argument in arguments for inference_id in argument["inference_ids"]}
    derived = {inference["output_statement_id"] for inference in inferences if inference["id"] in used_inferences}
    statuses: dict[str, str] = {}
    for statement_id in sorted(statement_by_id):
        proving = verifying.get(statement_id, [])
        if proving:
            status = "transcription" if all(result_id in transcription_results for result_id in proving) else "proved"
        elif statement_id in floor_met:
            status = "self-evident"
        elif statement_id in defended:
            status = "defended"
        elif statement_id in alternative_subjects:
            status = "alternative"
        elif statement_id in objection_subjects:
            status = "objection"
        elif statement_id in open_premises:
            status = "open"
        elif statement_id in derived:
            status = "derived"
        else:
            status = "source-only"
        statuses[statement_id] = status

    # Stages (#156, CATHOLICISM-SKELETON): a statement carries stage N when
    # stage N's conclusion rests on it through the inferences that output it,
    # their assumptions included.
    producers: dict[str, list[list[str]]] = {}
    for inference in inferences:
        producers.setdefault(inference["output_statement_id"], []).append(
            [*inference["input_statement_ids"], *inference.get("assumption_statement_ids", [])]
        )

    def rests_on(start: str) -> set[str]:
        seen = {start}
        pending = [start]
        while pending:
            for inputs in producers.get(pending.pop(), ()):
                for statement_id in inputs:
                    if statement_id not in seen:
                        seen.add(statement_id)
                        pending.append(statement_id)
        return seen

    stages = [
        {"stage": stage, "statement_id": statement_id}
        for stage, statement_id in STAGE_CONCLUSIONS
        if statement_id in statement_by_id
    ]
    statement_stages: dict[str, list[int]] = {}
    for entry in stages:
        for statement_id in sorted(rests_on(entry["statement_id"])):
            statement_stages.setdefault(statement_id, []).append(entry["stage"])

    # Default view target: the root when present, otherwise the verified
    # conclusion that rests on the most statements (ties by ID).
    default_target = root if root is not None and root in statement_by_id else None
    if default_target is None:
        best = 0
        verified = {result["argument_id"] for result in results}
        for conclusion in sorted(
            {argument["conclusion_statement_id"] for argument in arguments if argument["id"] in verified}
        ):
            size = len(rests_on(conclusion))
            if size > best:
                best, default_target = size, conclusion

    # The route-aware upward walk of every argument premise, closed or open:
    # the walk that gives an open item its transitive dependents.
    premise_dependents: dict[str, dict[str, list[str]]] = {}
    for statement_id in sorted({premise for argument in arguments for premise in argument["premise_statement_ids"]}):
        dependent_arguments, dependent_statements, _ = upward(statement_id)
        premise_dependents[statement_id] = {"arguments": dependent_arguments, "statements": dependent_statements}
    return {
        "statement_statuses": statuses,
        "stages": stages,
        "statement_stages": statement_stages,
        "default_target": default_target,
        "premise_dependents": premise_dependents,
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
        assembly = None if single else assembly_of(applied, hypothesis_names)
        opaque = opaque_atoms(groups, goal, definitions)
        short = len(steps) <= SHORT_PROOF_STEPS
        if goal_premises or single or assembly or opaque or short:
            flags.append(
                {
                    "result_id": result["id"],
                    "argument_id": result["argument_id"],
                    "proof_steps": len(steps),
                    "single_application_of": single,
                    "assembly_of": assembly,
                    "opaque_atoms": opaque,
                    "goal_consequent_premises": goal_premises,
                }
            )
    return flags


PROJECTION_RE = re.compile(r"^([A-Za-z_][\w']*)(?:\.(?:\d+|left|right|1|2|mp|mpr))*$")


def assembled_hypotheses(term: str, names: set[str]) -> list[str] | None:
    """Hypotheses a term only pairs together: an anonymous constructor or
    `And.intro` whose components are hypotheses (or their projections), or
    such terms nested. None when the term does anything else."""
    term = " ".join(term.split())
    while term.startswith("(") and term.endswith(")") and split_top_level(term[1:-1], ")")[0] == term[1:-1].strip():
        term = term[1:-1].strip()
    match = PROJECTION_RE.match(term)
    if match:
        return [match.group(1)] if match.group(1) in names else None
    if term.startswith("⟨") and term.endswith("⟩") and split_top_level(term[1:-1], "⟩")[0] == " ".join(term[1:-1].split()):
        parts = split_top_level(term[1:-1], ",")
    elif term.startswith("And.intro "):
        parts = split_top_level(term[len("And.intro ") :], " ")
    else:
        return None
    found: list[str] = []
    for part in parts:
        inner = assembled_hypotheses(part, names)
        if inner is None:
            return None
        found.extend(inner)
    return found


def assembly_of(applied: list[str], hypothesis_names: set[str]) -> list[str] | None:
    """Hypotheses a proof only assembles into a conjunction or tuple (#391):
    after leading `intro`s, optional destructuring of hypotheses (`obtain ⟨…⟩
    := h`, `rcases h with ⟨…⟩`), the proof is one anonymous constructor or
    `And.intro` of hypotheses (`⟨hClaims, hRose⟩`), or `constructor` followed
    only by `exact h` steps. Like a single application, such a proof only
    transcribes its premises (invariant 16)."""
    names = set(hypothesis_names)
    steps = list(applied)
    while steps:
        match = re.match(r"^(?:obtain\s+(⟨.*⟩)\s*:=\s*([A-Za-z_][\w']*)|rcases\s+([A-Za-z_][\w']*)\s+with\s+(⟨.*⟩))$", steps[0])
        if not match:
            break
        pattern = match.group(1) or match.group(4)
        source = match.group(2) or match.group(3)
        if source not in names:
            return None
        names.update(LEAN_IDENT_RE.findall(pattern))
        steps.pop(0)
    if not steps:
        return None
    if steps[0] == "constructor" and len(steps) >= 3:
        found: list[str] = []
        for step in steps[1:]:
            match = re.match(r"^(?:·\s*)?exact\s+(.+)$", step)
            inner = assembled_hypotheses(match.group(1), names) if match else None
            if inner is None:
                return None
            found.extend(inner)
        return found
    if len(steps) != 1:
        return None
    term = re.sub(r"^(?:exact|refine|apply)\s+", "", steps[0])
    found = assembled_hypotheses(term, names)
    return found if found is not None and len(found) >= 2 else None


LOGIC_IDENTIFIERS = {"True", "False", "Not", "And", "Or", "Iff"}


def propositional_over(expression: str, atoms: set[str], definitions: dict[str, tuple[list[str], str]], depth: int = 3) -> bool:
    """Whether an expression mentions only the given `Prop` atoms, logical
    constants and definitions whose bodies are themselves propositional over
    their parameters (unfolded up to `depth` levels)."""
    for name in LEAN_IDENT_RE.findall(expression):
        if name in atoms or name in LOGIC_IDENTIFIERS:
            continue
        tail = name.rsplit(".", 1)[-1]
        if depth and tail in definitions:
            params, body = definitions[tail]
            if params and propositional_over(body, set(params), definitions, depth - 1):
                continue
        return False
    return True


def opaque_atoms(
    groups: list[tuple[str, list[str], str]],
    goal: str,
    definitions: dict[str, tuple[list[str], str]],
) -> bool:
    """Opaque-atom heuristic (#391, invariant 16): every explicit parameter is
    a `Prop` atom or a hypothesis, there is at least one of each, and every
    hypothesis and the goal relate only those atoms through logical
    connectives and definitions that are propositional over their
    parameters (`def X (P Q : Prop) : Prop := P ∧ Q`). Nothing constrains
    such atoms, so the theorem certifies only that the step was transcribed.
    It is a warning, never a closure rule: declare the result's
    `transcription` field to make it count."""
    atoms: set[str] = set()
    hypotheses: list[str] = []
    for bracket, names, kind in groups:
        if kind == "Prop":
            atoms.update(names)
        elif bracket == "(":
            hypotheses.append(kind)
        elif kind.endswith("Type") or kind.startswith("Type") or kind.startswith("Sort"):
            return False
    if not atoms or not hypotheses or not goal:
        return False
    return all(propositional_over(kind, atoms, definitions) for kind in hypotheses + [goal])


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
        if item.get("bibliographic_claims"):
            lines.append(
                "  bibliographic witness, not byte-verified: " + ", ".join(item["bibliographic_claims"])
            )
        if item.get("transcription_premise_of"):
            lines.append(
                "  transcription premise of: " + ", ".join(item["transcription_premise_of"])
            )
        if item.get("floor_unmet"):
            unmet = item["floor_unmet"]
            lines.append(f"  self_evident basis {unmet['basis']} not met: {'; '.join(unmet['reasons'])}")
    floor = report.get("floor", [])
    lines.append("")
    lines.append(
        f"floor: {sum(entry['met'] for entry in floor)} of {len(floor)} self_evident markings meet their basis "
        "(closure is relative to these bases)"
    )
    for entry in floor:
        status = "met" if entry["met"] else "not met: " + "; ".join(entry["reasons"])
        lines.append(f"  {entry['statement_id']} [{entry['basis']}]: {status}")
    lines.extend(format_floor_bases(report.get("routes", {})))
    uncounted =[refutation for refutation in report.get("refutations", []) if not refutation["counted"]]
    if uncounted:
        lines.append("")
        lines.append(f"refutations not counted for rule (c): {len(uncounted)}")
        for refutation in uncounted:
            reason = (
                "no verified result"
                if not refutation["verified"]
                else "open premises " + ", ".join(refutation["open_premise_statement_ids"])
            )
            lines.append(f"  {refutation['relation_id']} ({refutation['argument_id']} refutes {refutation['statement_id']}): {reason}")
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
        f"(single application, assembly of hypotheses, opaque Prop atoms, goal as premise consequent, "
        f"or at most {SHORT_PROOF_STEPS} proof steps)"
    )
    kinds = report.get("transcription_results", {})
    for flag in flags:
        notes = [f"{flag['proof_steps']} steps"]
        kind = kinds.get(flag["result_id"])
        if kind and kind["declared"]:
            notes.append(f"declared transcription: {kind['kind']}")
        if flag["single_application_of"]:
            notes.append(f"single application of {flag['single_application_of']}")
        if flag.get("assembly_of"):
            notes.append(f"assembly of {', '.join(flag['assembly_of'])}")
        if flag.get("opaque_atoms"):
            notes.append("opaque Prop atoms")
        for premise in flag["goal_consequent_premises"]:
            ids = ", ".join(premise["statement_ids"]) or "no statement match"
            notes.append(f"goal is consequent of {premise['hypothesis']} ({ids})")
        lines.append(f"  {flag['result_id']}: {'; '.join(notes)}")
    return "\n".join(lines)


def format_routes(routes: dict[str, Any]) -> str:
    entries = routes["routes"]
    lines = [
        f"routes to {routes['root']}: {len(entries)} arguments; cheapest "
        f"{routes['cheapest_argument_id'] or 'none (no verified route)'}"
    ]
    if not entries:
        return "\n".join(lines)
    lines.append("cost  premises  argument")
    for entry in entries:
        marks = [
            mark
            for mark, present in (
                ("cheapest", entry["cheapest"]),
                ("designated", entry["designated"]),
                ("unverified", not entry["verified"]),
                ("transcription", entry["transcription"]),
            )
            if present
        ]
        suffix = f"  [{', '.join(marks)}]" if marks else ""
        lines.append(f"{entry['cost']:>4}  {entry['premise_count']:>8}  {entry['argument_id']}{suffix}")
    for entry in entries:
        if not entry["cheapest"]:
            continue
        lines.append("")
        lines.append(f"open premises of the cheapest route {entry['argument_id']} ({entry['cost']}):")
        for statement_id in entry["open_premise_statement_ids"]:
            note = " (proved, rests on open premises)" if statement_id in entry["proved_unestablished_statement_ids"] else ""
            lines.append(f"  {statement_id}{note}")
    lines.extend(format_floor_bases(routes))
    return "\n".join(lines)


def format_floor_bases(routes: dict[str, Any]) -> list[str]:
    """The root report's floor line (#500): closure is relative to these bases."""
    bases = routes.get("floor_bases", [])
    rendered = ", ".join(f"{entry['statement_id']} ({entry['basis']})" for entry in bases)
    return ["", f"closed relative to floor bases: {rendered or 'none'}"]


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


def validate_result_config(path: Path, result: dict[str, Any], argument_ids: Iterable[str]) -> dict[str, Any]:
    """One result/provenance contract shared by corpus and configuration gates."""
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
    if result["argument_id"] not in argument_ids:
        raise CorpusError(
            f"{path.relative_to(ROOT)}: unknown argument_id {result['argument_id']}"
        )
    validate_result_transcription(path.relative_to(ROOT), result)
    challenge = module_path(result["challenge_module"])
    solution = module_path(result["solution_module"])
    canonical = f"results/{result['id']}/comparator.json"
    if result["comparator_config"] != canonical:
        raise CorpusError(f"{path.relative_to(ROOT)}: Comparator path must match executable gate: {canonical}")
    config_path = ROOT / canonical
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
    axiom_error = permitted_axioms_error(config)
    if axiom_error:
        raise CorpusError(f"{config_path.relative_to(ROOT)}: {axiom_error}")
    if config.get("enable_nanoda") is not True:
        raise CorpusError(
            f"{config_path.relative_to(ROOT)}: NanoDa must be enabled"
        )
    return config


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
    attempts = load_dir("attempts")

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
    attempt_index = index_by_id(attempts, "attempt")
    models = registered_models(statement_index)
    registered_configurations(
        {sid: record for sid, (_, record) in statement_index.items()},
        {rid: record for rid, (_, record) in result_index.items()},
        {aid: record for aid, (_, record) in argument_index.items()},
        {model["id"]: model for model in models},
    )
    for path, attempt in attempts:
        try:
            validate_attempt(attempt, set(statement_index), set(result_index) | set(claim_index))
        except ValueError as exc:
            raise CorpusError(f"{path.relative_to(ROOT)}: {exc}") from exc
        validate_prose_ids(path, attempt, ("summary", "blocker"), set(statement_index) | set(definition_index) | set(disambiguation_index))
    definition_ids = set(definition_index)
    disambiguation_ids = set(disambiguation_index)
    used_definitions: set[str] = set()

    for path, field, _ in unsorted_lists():
        raise CorpusError(
            f"{path.relative_to(ROOT)}: {field} must be sorted; run python3 scripts/corpus.py sort-lists"
        )

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
        validate_self_evident(path, statement, claim_ids, result_ids, set(statement_index))
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

    result_configs = {result["id"]: validate_result_config(path, result, argument_index) for path, result in results}

    result_records = {key: value[1] for key, value in result_index.items()}
    for path, relation in relations:
        validate_schema_registration(path, relation, result_records, result_configs)

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
        "attempts": len(attempt_index),
        "models": len(models),
    }


def check_warnings() -> list[str]:
    """Closure-integrity warnings (#391): unflagged opaque-atom candidates,
    `refutes` relations that do not count because their argument is
    unverified or rests on open premises, and self_evident markings whose
    floor basis is not met by the current records (#500)."""
    statements = [record for _, record in load_dir("statements")]
    arguments = [record for _, record in load_dir("arguments")]
    results = [record for _, record in load_dir("results")]
    relations = [record for _, record in load_dir("relations")]
    claims = [record for _, record in load_dir("claims")]
    flags = transcription_flags(results, arguments, statements)
    declared = {result["id"] for result in results if result.get("transcription")}
    warnings = [
        f"{flag['result_id']}: every proposition the theorem relates looks like an unconstrained "
        "`Prop` atom (invariant 16); declare \"transcription\": \"opaque_atoms\" or type the vocabulary"
        for flag in flags
        if flag.get("opaque_atoms") and flag["result_id"] not in declared
    ]
    report = frontier_report(
        statements, arguments, results, relations, root=None, transcription=flags, claims=claims
    )
    for refutation in report["refutations"]:
        if refutation["counted"]:
            continue
        if not refutation["verified"]:
            reason = "its argument has no verified result"
        else:
            reason = "it rests on open premises " + ", ".join(refutation["open_premise_statement_ids"])
        warnings.append(
            f"{refutation['relation_id']}: refutation of {refutation['statement_id']} does not count "
            f"for closure rule (c): {reason}"
        )
    for entry in report["floor"]:
        if not entry["met"]:
            warnings.append(
                f"{entry['statement_id']}: self_evident basis {entry['basis']} is not met, so the marking "
                f"closes nothing: {'; '.join(entry['reasons'])}"
            )
    return warnings


def command_check(_: argparse.Namespace) -> int:
    counts = validate()
    for warning in check_warnings():
        print(f"warning: {warning}", file=sys.stderr)
    print(
        "corpus ok: "
        f"{counts['sources']} sources, {counts['passages']} passages, "
        f"{counts['statements']} statements, {counts['claims']} claims, "
        f"{counts['inferences']} inferences, {counts['arguments']} arguments, "
        f"{counts['relations']} relations, {counts['results']} results, "
        f"{counts['candidates']} candidates, {counts['definitions']} definitions, "
        f"{counts['disambiguations']} disambiguations, {counts['attempts']} attempts, {counts['models']} models"
    )
    return 0


def command_sort_lists(_: argparse.Namespace) -> int:
    for path, field, raw in unsorted_lists():
        record = json.loads(raw)
        record[field] = sorted(record[field])
        indent = 2 if '\n  "' in raw else None
        path.write_text(json.dumps(record, ensure_ascii=False, indent=indent) + "\n", encoding="utf-8")
        print(f"sorted {field} in {path.relative_to(ROOT)}")
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
        "attempts",
        "models",
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
        inferences=[record for _, record in load_dir("inferences")],
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
    if args.routes:
        if args.json:
            print(json.dumps(report["routes"], indent=2, ensure_ascii=False))
        else:
            print(format_routes(report["routes"]))
        return 0
    if args.json:
        print(json.dumps(report, indent=2, ensure_ascii=False))
    else:
        print(format_frontier(report))
    return 0


def command_territory(args: argparse.Namespace) -> int:
    """Emergent positions and the territory matrix (#512); writes no record."""
    validate()
    names = ("statements", "arguments", "results", "relations", "claims", "sources", "inferences")
    data = {name: [record for _, record in load_dir(name)] for name in names}
    report = frontier_report(
        data["statements"], data["arguments"], data["results"], data["relations"], root=args.root,
        transcription=transcription_flags(data["results"], data["arguments"], data["statements"]),
        claims=data["claims"], inferences=data["inferences"],
    )
    if not report["root_known"]:
        raise CorpusError(f"unknown root statement: {args.root}")
    territory = territory_report(
        statements={record["id"]: record for record in data["statements"]},
        arguments={record["id"]: record for record in data["arguments"]},
        results={record["id"]: record for record in data["results"]},
        relations=data["relations"],
        claims=data["claims"],
        sources={record["id"]: record for record in data["sources"]},
        models=registered_models(),
        transcription_results=set(report["transcription_results"]),
        seeds=[item for item in report["items"] if item["path_to_root"] is not None],
        routes=report["routes"]["routes"],
        max_atoms=args.max_atoms,
    )
    territory["root"] = args.root
    if args.json:
        print(json.dumps(territory, indent=2, ensure_ascii=False, sort_keys=True))
    else:
        print(format_territory(territory))
    return 0


def command_related(args: argparse.Namespace) -> int:
    # Discovery is independent of expensive proof gates and frontier computation.
    import sqlite3
    from research_index import cached_related
    try:
        report = cached_related(ROOT, args.statement_id, args.limit)
    except (ValueError, OSError, sqlite3.Error) as exc:
        raise CorpusError(str(exc)) from exc
    if args.json:
        print(json.dumps(report, indent=2, ensure_ascii=False))
    else:
        print(f"Related to {report['statement_id']} (discovery, not certification)")
        for item in report['matches']:
            print(f"\n{item['statement_id']}: {item['paraphrase']}")
            print(f"  {item['path']}")
            for reason in item['reasons'][:3]:
                evidence = reason.get('argument_id') or reason.get('relation_id') or ', '.join(reason.get('ids', [])) or reason.get('declaration') or reason.get('namespace') or ', '.join(reason.get('words', []))
                print(f"  {reason['kind']}: {evidence}")
                if 'premise_statement_ids' in reason:
                    print('    requires: ' + ', '.join(reason['premise_statement_ids']))
                    print('    concludes: ' + str(reason['conclusion_statement_id']))
            if item['reason_count'] > 3:
                print(f"  {item['reason_count']} reasons total; showing 3 (all in --json)")
        print('\nPrior attempts:')
        for attempt in report['prior_attempts']:
            print(f"  {attempt['id']} [{attempt['outcome']}]: {attempt['path']}")
        if not report['prior_attempts']:
            print('  none directly linked')
        print('\nUse dossier for premise status and configurations for certification.')
    return 0


def command_dossier(args: argparse.Namespace) -> int:
    validate()
    directories = ("statements", "claims", "definitions", "disambiguations", "inferences", "arguments", "results", "relations", "attempts", "models", "configurations")
    data = {name: [record for _, record in load_dir(name)] for name in directories}
    if not args.all and args.statement_id not in {entry["id"] for entry in data["statements"]}:
        raise CorpusError(f"unknown statement: {args.statement_id}")
    report = frontier_report(data["statements"], data["arguments"], data["results"], data["relations"],
                             root=args.root, transcription=transcription_flags(data["results"], data["arguments"], data["statements"]), claims=data["claims"])
    if not report["root_known"]:
        raise CorpusError(f"unknown root statement: {args.root}")
    dossiers = dossier_index(data, report)
    if args.all:
        print(json.dumps(dossiers, ensure_ascii=False))
        return 0
    if args.statement_id not in dossiers:
        raise CorpusError(f"unknown statement: {args.statement_id}")
    dossier = dossiers[args.statement_id]
    print(json.dumps(dossier, indent=2, ensure_ascii=False) if args.json else format_dossier(dossier, data))
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


def bind_report(
    described_list: list[dict[str, Any]],
    schema_bindings: Iterable[tuple[dict[str, Any], dict[str, Any]]] = (),
) -> dict[str, Any]:
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
    for binding, argument in schema_bindings:
        described = by_theorem.get(binding["theorem"], {"error": "schema theorem not described by the Lean tool"})
        entry = bind_result(binding, argument, statement_index, described)
        entry["kind"] = "schema-registration"
        entries.append(entry)
    used = {tuple(item["pin"]) for entry in entries for item in entry["undecidable"]}
    stale = sorted(list(key) for key in PINNED_UNDECLARED_BINDINGS if key not in used)
    summary = Counter(entry["status"] for entry in entries)
    return {
        "summary": {status: summary.get(status, 0) for status in ("bound", "pinned", "mismatch")},
        "stale_pins": stale,
        "results": entries,
    }


def registered_configurations(statements=None, results=None, arguments=None, models=None):
    statements = statements if statements is not None else {r["id"]: r for _, r in load_dir("statements")}
    results = results if results is not None else {r["id"]: r for _, r in load_dir("results")}
    arguments = arguments if arguments is not None else {r["id"]: r for _, r in load_dir("arguments")}
    models = models if models is not None else {model["id"]: model for model in registered_models()}
    records = load_dir("configurations")
    index_by_id(records, "configuration")
    selected = sorted({rid for _, case in records for field in ("incompatibility_result_ids", "implication_result_ids") for rid in case.get(field, []) if isinstance(rid, str)})
    for rid in selected:
        if rid in results:
            validate_result_config(CORPUS / "results" / f"{rid}.json", results[rid], arguments)
    if any(case.get("implication_result_ids") for _, case in records):
        flags = transcription_flags(list(results.values()), list(arguments.values()), list(statements.values()))
        transcriptions = transcription_kinds(list(results.values()), flags)
        for path, case in records:
            rejected = set(case.get("implication_result_ids", [])) & transcriptions.keys()
            if rejected:
                raise CorpusError(f"{path.relative_to(ROOT)}: transcriptions cannot supply deductions: {sorted(rejected)}")
    for path, case in records:
        try:
            validate_case(case, statements, results, arguments, models, ROOT)
        except ValueError as exc:
            raise CorpusError(f"{path.relative_to(ROOT)}: {exc}") from exc
    return [case for _, case in records]


def configuration_context():
    statements = {r["id"]: r for _, r in load_dir("statements")}
    results = {r["id"]: r for _, r in load_dir("results")}
    arguments = {r["id"]: r for _, r in load_dir("arguments")}
    models = {model["id"]: model for model in registered_models()}
    cases = registered_configurations(statements, results, arguments, models)
    return dict(statements=statements, results=results, arguments=arguments, models=models, cases=cases)


def collect_configuration_reports(args: argparse.Namespace, context=None):
    context = configuration_context() if context is None else context
    statements, results, arguments, models, cases = (context[key] for key in ("statements", "results", "arguments", "models", "cases"))
    if args.case:
        cases = [case for case in cases if case["id"] == args.case]
        if not cases:
            raise CorpusError(f"unknown configuration case {args.case}")
    if args.seed:
        if args.seed not in statements:
            raise CorpusError(f"unknown statement {args.seed}")
        cases = [case for case in cases if case["seed_statement_id"] == args.seed]
    if args.premise and len(cases) != 1:
        raise CorpusError("--premise requires exactly one selected case")
    reports = []
    verified_results: set[str] = set()
    original_result_ids: set[str] = set()
    for case in cases:
        selection = None
        if args.premise:
            if len(args.premise) != len(set(args.premise)) or any(sid not in case["semantics"]["applications"] for sid in args.premise):
                raise CorpusError("premises must be unique explicit statement IDs in this profile")
            selection = {"id": "selection", "statement_ids": args.premise}
        try:
            verification = None if args.registered else verify_case(case, statements, results, arguments, models, ROOT, verified_results)
            if verification is not None:
                original_result_ids.update(case.get("incompatibility_result_ids", []) + case.get("implication_result_ids", []))
                verification["original_bound_result_ids"] = sorted(set(case.get("incompatibility_result_ids", []) + case.get("implication_result_ids", [])))
            report = configuration_report(case, results, arguments, models, verified=verification is not None, selection=selection)
            if verification is not None:
                verification["compositions"] = verify_compositions(case, report, statements, results, arguments, ROOT)
        except ValueError as exc:
            raise CorpusError(str(exc)) from exc
        report["verification"] = verification
        reports.append(report)
    if original_result_ids:
        # Every selected case has now built and verified its modules. Describe the
        # unique original theorems together, avoiding repeated Lean startup/imports;
        # no report escapes if any original binding fails.
        originals = [results[rid] for rid in sorted(original_result_ids)]
        descriptions = {entry["theorem"]: entry for entry in run_bind_tool(bind_tool_input([(ROOT, result) for result in originals]))}
        statement_index = {sid: (ROOT, statement) for sid, statement in statements.items()}
        for result in originals:
            binding = bind_result(result, arguments[result["argument_id"]], statement_index,
                                  descriptions.get(result["theorem"], {"error": "missing original theorem description"}))
            if binding["status"] != "bound":
                raise CorpusError(f"{result['id']}: original theorem binding rejected: {binding['problems']}")
    return reports


def command_configurations(args: argparse.Namespace) -> int:
    reports = collect_configuration_reports(args)
    if args.json:
        print(json.dumps(reports, indent=2, ensure_ascii=False, sort_keys=True))
    else:
        for report in reports:
            print(f"{report['id']}: semantics {report['semantics']['id']}")
            print(report['scope'])
            for model in report['inapplicable_models']:
                print(f"  inapplicable model {model['model_id']}: {model['profile_mismatches']}")
            for entry in report['configurations']:
                print(f"  {entry['id']}: {entry['status']}; premises {entry['statement_ids']}")
                for core in entry['incompatible_cores']:
                    print(f"    core {core['statement_ids']}: {core['result_id']} / {core['theorem']}; {core['minimality']}")
                    print(f"    certificate chain: {core['result_ids']}")
                for model in entry['model_witnesses']:
                    print(f"    model: {model['model_id']} / {model['lean_declaration']}")
                    for evaluation in model['evaluations']:
                        print(f"      {evaluation['statement_id']}: {evaluation['theorem']}")
                if entry['unresolved_reason']:
                    print(f"    {entry['unresolved_reason']}")
                if entry['consequences']:
                    for consequence in entry['consequences']['items']:
                        print(f"    consequence {consequence['statement_id']}: {consequence['sufficient_subsets']}")
    return 0


def command_configuration_report(args: argparse.Namespace) -> int:
    from configuration_explorer import input_manifest, read_bundle, write_bundle
    try:
        if args.build_input:
            import os
            artifact = os.environ.get("TRUTH_CORE_CONFIGURATION_REPORT")
            if not artifact:
                if os.environ.get("TRUTH_CORE_REQUIRE_CONFIGURATION_REPORT") == "true":
                    raise CorpusError("certified build requires TRUTH_CORE_CONFIGURATION_REPORT")
                print(json.dumps({"mode": "registered-only"}) if args.json else "configuration build input: registered-only development")
                return 0
            path = Path(artifact)
            path = path if path.is_absolute() else ROOT / path
            if path.resolve() != (ROOT / ".cache/configuration-explorer.json").resolve():
                raise CorpusError("certified build report must use .cache/configuration-explorer.json for cache invalidation")
            bundle = read_bundle(ROOT, path, configuration_context())
        elif args.check:
            path = Path(args.check)
            bundle = read_bundle(ROOT, path if path.is_absolute() else ROOT / path, configuration_context())
        else:
            initial = input_manifest(ROOT)
            context = configuration_context()
            selection = argparse.Namespace(case=None, seed=None, premise=[], registered=False)
            reports = collect_configuration_reports(selection, context)
            output = Path(args.output)
            bundle = write_bundle(ROOT, output if output.is_absolute() else ROOT / output, context, reports, initial)
    except ValueError as exc:
        raise CorpusError(str(exc)) from exc
    if args.json:
        # Input hashes stay server-side; the UI needs source identity and data.
        projection = {**bundle, "producer": {key: value for key, value in bundle["producer"].items() if key != "inputs"}}
        print(json.dumps(projection, indent=2, ensure_ascii=False, sort_keys=True))
    else:
        print(f"configuration report: {len(bundle['cases'])} cases; source {bundle['producer']['source_head']}; input digest {bundle['producer']['input_digest']}")
        print("Validated producer output freshness; this check is not fresh proof execution." if args.check or args.build_input else "Live verification completed; disposable producer output written.")
    return 0


def registered_models(statement_index=None):
    if statement_index is None:
        statement_index = index_by_id(load_dir("statements"), "statement")
    records = load_dir("models")
    index_by_id(records, "model")
    for path, model in records:
        try:
            validate_model(model, {sid: record for sid, (_, record) in statement_index.items()}, ROOT)
        except ValueError as exc:
            raise CorpusError(f"{path.relative_to(ROOT)}: {exc}") from exc
    return [model for _, model in records]


def command_models(args: argparse.Namespace) -> int:
    statements = {r["id"]: r for _, r in load_dir("statements")}
    if args.argument:
        arguments = {r["id"]: r for _, r in load_dir("arguments")}
        if args.argument not in arguments:
            raise CorpusError(f"unknown argument {args.argument}")
        argument = arguments[args.argument]
        if args.check and args.check != argument["conclusion_statement_id"]:
            raise CorpusError("--argument conclusion must match --check")
        args.check = argument["conclusion_statement_id"]
        args.premise = sorted(set(args.premise) | set(argument["premise_statement_ids"]))
    if args.premise and not args.check:
        raise CorpusError("--premise requires --check or --argument")
    for sid in ([args.check] if args.check else []) + args.premise:
        if sid not in statements:
            raise CorpusError(f"unknown statement {sid}")
    models = registered_models()
    report = model_report(models, args.check, args.premise)
    report["argument_id"] = args.argument
    if args.verify or args.check:
        try:
            report["verification"] = verify_models(models, statements, ROOT)
        except ValueError as exc:
            raise CorpusError(str(exc)) from exc
    if args.json:
        print(json.dumps(report, indent=2, ensure_ascii=False, sort_keys=True))
    else:
        print(report["scope"])
        print("Premises: " + (", ".join(report["premise_statement_ids"]) or "none (empty premise set)"))
        for model in report["models"]:
            print(f"{model['id']}: {model['target_value'] or 'registered'}; {model['classification']}; vocabulary {model['vocabulary']}")
            print(f"  Lean model: {model['lean_declaration']}")
            for evaluation in model['evaluations']:
                print(f"  {evaluation['value']} {evaluation['statement_id']}: {evaluation['theorem']}")
            if model['missing_premises'] or model['violated_premises']:
                print(f"  unknown premises: {model['missing_premises']}; violated premises: {model['violated_premises']}")
        if not report["models"]:
            print("No registered evaluation; no conclusion about derivability or consistency.")
        for pattern in report['cofailure_candidates']:
            print(f"Candidate co-failure only: {pattern['statement_ids']} in {pattern['vocabulary']}; models {pattern['model_ids']}")
        if args.verify or args.check:
            print(f"model-check: {report['verification']}")
    return 0


def command_bind_check(args: argparse.Namespace) -> int:
    validate()
    results = load_dir("results")
    schema_bindings = schema_binding_records(
        [relation for _, relation in load_dir("relations")],
        {record["id"]: record for _, record in results},
    )
    if args.lean_json:
        described_list = json.loads(Path(args.lean_json).read_text(encoding="utf-8"))
    else:
        described_list = run_bind_tool(bind_tool_input(
            results + [(ROOT, binding) for binding, _ in schema_bindings]
        ))
    report = bind_report(described_list, schema_bindings)
    if not args.lean_json:
        try:
            report["models"] = verify_models(registered_models(), {r["id"]: r for _, r in load_dir("statements")}, ROOT)
        except ValueError as exc:
            raise CorpusError(str(exc)) from exc
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


# --- unused-premises (#571): result proofs that ignore a listed premise ---------

UNUSED_TOOL = ROOT / "scripts" / "UnusedPremises.lean"


def run_unused_tool(tool_input: dict[str, list[str]]) -> list[dict[str, Any]]:
    """Run scripts/UnusedPremises.lean (same input as BindTypes.lean; needs `lake build`)."""
    import subprocess
    import tempfile

    with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False, encoding="utf-8") as handle:
        json.dump(tool_input, handle)
        input_path = handle.name
    try:
        completed = subprocess.run(
            ["lake", "env", "lean", "--run", str(UNUSED_TOOL), input_path],
            cwd=ROOT, capture_output=True, text=True, check=False,
        )
    except FileNotFoundError as exc:
        raise CorpusError("unused-premises needs `lake` on PATH (run after `lake build`)") from exc
    finally:
        Path(input_path).unlink(missing_ok=True)
    if completed.returncode != 0:
        raise CorpusError(
            f"{UNUSED_TOOL.relative_to(ROOT)} failed (exit {completed.returncode}):\n"
            f"{completed.stderr.strip() or completed.stdout.strip()}"
        )
    try:
        described = json.loads(completed.stdout)
    except json.JSONDecodeError as exc:
        raise CorpusError(f"{UNUSED_TOOL.relative_to(ROOT)} printed invalid JSON: {exc}") from exc
    if not isinstance(described, list):
        raise CorpusError(f"{UNUSED_TOOL.relative_to(ROOT)} must print a JSON array")
    return described


def unused_premise_findings(
    bind_entries: list[dict[str, Any]],
    usage_list: list[dict[str, Any]],
    root_open: set[str] | frozenset[str] = frozenset(),
) -> dict[str, Any]:
    """Join bind-check's premise binding with the proof-term usage report.

    A finding is a premise statement bound (by bind-check) to a hypothesis, or
    to a conjunct of a theory-bundle hypothesis, that the proof never uses.
    Results that bind-check does not bind (status `mismatch`) are skipped and
    listed, since their premises have no reliable hypothesis positions.
    `root_open` is the set of open premises from which the root is reached.
    """
    usage = {entry.get("theorem"): entry for entry in usage_list}
    findings: list[dict[str, Any]] = []
    skipped: list[str] = []
    checked = 0
    for entry in bind_entries:
        if entry.get("kind") == "schema-registration":
            continue
        described = usage.get(entry["theorem"])
        if entry["status"] == "mismatch" or described is None or "error" in described:
            skipped.append(entry["id"])
            continue
        checked += 1
        by_position = {item["position"]: item for item in described["hypotheses"]}
        for premise in entry["premises"]:
            item = by_position.get(premise["position"])
            if item is None:
                skipped.append(entry["id"])
                break
            if "conjunct" in premise:
                flags = item.get("conjuncts_used")
                used = flags[premise["conjunct"]] if isinstance(flags, list) else True
            else:
                used = item["used"]
            if used:
                continue
            finding = {
                "result_id": entry["id"],
                "theorem": entry["theorem"],
                "hypothesis": premise["hypothesis"],
                "statement_id": premise["statement_id"],
                "open_on_root_path": premise["statement_id"] in root_open,
            }
            if "conjunct" in premise:
                finding["bundle"] = premise["bundle"]
                finding["conjunct"] = premise["conjunct"]
            findings.append(finding)
    return {
        "summary": {"checked": checked, "findings": len(findings), "skipped": len(skipped)},
        "findings": findings,
        "skipped": sorted(set(skipped)),
    }


def command_unused_premises(args: argparse.Namespace) -> int:
    validate()
    results = load_dir("results")
    if args.bind_json:
        bind_entries = json.loads(Path(args.bind_json).read_text(encoding="utf-8"))["results"]
    else:
        bind_entries = bind_report(run_bind_tool(bind_tool_input(results)))["results"]
    if args.usage_json:
        usage_list = json.loads(Path(args.usage_json).read_text(encoding="utf-8"))
    else:
        usage_list = run_unused_tool(bind_tool_input(results))
    names = ("statements", "arguments", "results", "relations", "claims", "inferences")
    data = {name: [record for _, record in load_dir(name)] for name in names}
    frontier = frontier_report(
        data["statements"], data["arguments"], data["results"], data["relations"], root=args.root,
        transcription=transcription_flags(data["results"], data["arguments"], data["statements"]),
        claims=data["claims"], inferences=data["inferences"],
    )
    root_open = {item["statement_id"] for item in frontier["items"] if item["path_to_root"] is not None}
    report = unused_premise_findings(bind_entries, usage_list, root_open)
    if args.json:
        print(json.dumps(report, indent=2, ensure_ascii=False, sort_keys=True))
    else:
        for finding in report["findings"]:
            where = f" (conjunct {finding['conjunct'] + 1} of {finding['bundle']})" if "bundle" in finding else ""
            root = " [open, on root path]" if finding["open_on_root_path"] else ""
            print(f"unused: {finding['result_id']}: {finding['statement_id']} via {finding['hypothesis']}{where}{root}")
        for result_id in report["skipped"]:
            print(f"skipped: {result_id} (not bound by bind-check)")
        summary = report["summary"]
        print(
            f"unused-premises: {summary['checked']} results checked, {summary['findings']} unused premise(s), "
            f"{summary['skipped']} skipped"
        )
    return 1 if args.strict and report["findings"] else 0


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description="Inspect and validate the truth-core corpus")
    sub = result.add_subparsers(dest="command", required=True)
    sub.add_parser("check", help="validate corpus references, source evidence, and Comparator configs").set_defaults(
        func=command_check
    )
    configuration_report_parser = sub.add_parser("configuration-report", help="produce or freshness-check disposable verified explorer output")
    report_mode = configuration_report_parser.add_mutually_exclusive_group(required=True)
    report_mode.add_argument("--build-input", action="store_true", help="uncached build preflight: validate explicit certified mode or registered-only development")
    report_mode.add_argument("--output", metavar="PATH", help="live-verify and atomically write an ignored .cache bundle")
    report_mode.add_argument("--check", metavar="PATH", help="check trusted producer output freshness/projection; does not rerun proofs")
    configuration_report_parser.add_argument("--json", action="store_true")
    configuration_report_parser.set_defaults(func=command_configuration_report)
    configurations = sub.add_parser("configurations", help="compose explicit configurations with live certified cores/models")
    configurations.add_argument("--case", metavar="CONFIG-ID")
    configurations.add_argument("--seed", metavar="STMT-ID")
    configurations.add_argument("--premise", action="append", default=[], metavar="STMT-ID")
    configurations.add_argument("--registered", action="store_true", help="display inputs only; no certified status without live verification")
    configurations.add_argument("--json", action="store_true")
    configurations.set_defaults(func=command_configurations)
    models = sub.add_parser("models", help="inspect registered finite interpretations (no premise closure)")
    models.add_argument("--check", metavar="STMT-ID", help="target statement")
    models.add_argument("--premise", action="append", default=[], metavar="STMT-ID", help="require this premise (repeatable; default empty set)")
    models.add_argument("--argument", metavar="ARG-ID", help="use an existing argument conclusion and its complete premise set")
    models.add_argument("--verify", action="store_true", help="Lean-check exact evaluations, finite carriers and zero axioms after lake build")
    models.add_argument("--json", action="store_true")
    models.set_defaults(func=command_models)
    sub.add_parser("status", help="show corpus counts").set_defaults(func=command_status)
    sub.add_parser(
        "sort-lists", help="sort order-free lists (SORTED_LIST_FIELDS) in place, as check requires"
    ).set_defaults(func=command_sort_lists)
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
    frontier.add_argument(
        "--routes",
        action="store_true",
        help="print the open-premise cost of each argument concluding the root, cheapest marked",
    )
    frontier.set_defaults(func=command_frontier)
    territory = sub.add_parser(
        "territory",
        help="emergent positions and territory matrix from certified cores, models and claims (no hand-authored worldviews)",
    )
    territory.add_argument("--json", action="store_true", help="print the deterministic report as JSON")
    territory.add_argument("--root", default=DEFAULT_FRONTIER_ROOT)
    territory.add_argument("--max-atoms", type=int, default=512, help="bound on the atom universe (default 512)")
    territory.set_defaults(func=command_territory)
    related_parser = sub.add_parser("related", help="find connected propositions and previous attempts; discovery only")
    related_parser.add_argument("statement_id")
    related_parser.add_argument("--limit", type=int, default=10)
    related_parser.add_argument("--json", action="store_true")
    related_parser.set_defaults(func=command_related)
    dossier = sub.add_parser("dossier", help="inspect a premise's sources, arguments, attempts and route contribution")
    target = dossier.add_mutually_exclusive_group(required=True)
    target.add_argument("statement_id", nargs="?")
    target.add_argument("--all", action="store_true", help="emit all dossiers as one JSON object (for the explorer)")
    dossier.add_argument("--json", action="store_true", help="print machine-readable JSON")
    dossier.add_argument("--root", default=DEFAULT_FRONTIER_ROOT)
    dossier.set_defaults(func=command_dossier)
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
    unused = sub.add_parser(
        "unused-premises",
        help="report result premises whose bound hypothesis the proof term never uses (after lake build)",
    )
    unused.add_argument("--json", action="store_true", help="print the deterministic report as JSON")
    unused.add_argument("--strict", action="store_true", help="exit 1 when any unused premise is found")
    unused.add_argument("--root", default=DEFAULT_FRONTIER_ROOT, help="root for the on-root-path flag")
    unused.add_argument("--bind-json", help="use a saved `bind-check --json` report instead of running Lean")
    unused.add_argument("--usage-json", help="use a saved scripts/UnusedPremises.lean output instead of running Lean")
    unused.set_defaults(func=command_unused_premises)
    structure = sub.add_parser("structure", help="inspect elaborated proposition structure (derived presentation only)")
    structure.add_argument("statement_id")
    structure.add_argument("--json", action="store_true", help="emit JSON (the structural format)")
    structure.add_argument("--unfold", action="append", default=[], metavar="DECLARATION", help="unfold exactly one project definition, explicitly")
    structure.set_defaults(func=command_structure)
    report = sub.add_parser("structure-report", help="generate or validate the first-slice explorer structure artifact")
    report.add_argument("--output", default=".cache/proposition-structure.json")
    report.add_argument("--build-input", action="store_true", help="generate the explorer input (default)")
    report.add_argument("--check-input", action="store_true", help="validate existing artifact input hashes without Lean")
    report.set_defaults(func=command_structure)
    return result


def command_structure(args: argparse.Namespace) -> int:
    from proposition_structure import FIRST_SLICE, build_reports, check_artifact

    try:
        output = ROOT / getattr(args, "output", ".cache/proposition-structure.json")
        if getattr(args, "check_input", False):
            check_artifact(ROOT, json.loads(output.read_text()))
            print("structure artifact inputs match")
            return 0
        kinds = ("statements", "definitions", "disambiguations", "arguments", "results", "relations", "claims", "inferences")
        records = {kind: load_dir(kind) for kind in kinds}
        data = {kind: [r for _, r in values] for kind, values in records.items()}
        frontier = frontier_report(data["statements"], data["arguments"], data["results"], data["relations"],
                                   transcription=transcription_flags(data["results"], data["arguments"], data["statements"]),
                                   claims=data["claims"], inferences=data["inferences"])
        batch = args.command == "structure-report"
        selected = list(FIRST_SLICE) if batch else [args.statement_id]
        unfold = list(getattr(args, "unfold", []))
        if batch:
            unfold.extend(s["lean_declaration"] for s in data["statements"] if s["id"] in selected)
            unfold.append("TruthCore.Case.Catholicism.ClassicalAttributesSuffice")
        report = build_reports(ROOT, records, selected, unfold, frontier)
        if batch:
            output.parent.mkdir(parents=True, exist_ok=True)
            output.write_text(json.dumps(report, ensure_ascii=False) + "\n")
            print(f"wrote {output}")
        else:
            print(json.dumps(report["reports"][0], indent=2, ensure_ascii=False))
        return 0
    except (ValueError, OSError, KeyError) as exc:
        raise CorpusError(str(exc)) from exc


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
