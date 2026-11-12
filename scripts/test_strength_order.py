#!/usr/bin/env python3
"""Strength order between sibling versions (#1017). Run with:

    python3 -m unittest discover -s scripts -p 'test_*.py'
"""

from __future__ import annotations

import json
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import corpus  # noqa: E402
from corpus_ids import legacy_uuid  # noqa: E402


def statement(statement_id: str, **extra: object) -> dict[str, object]:
    return {"id": statement_id, "paraphrase": statement_id.lower(), **extra}


def argument(argument_id: str, premises: list[str], conclusion: str, **extra: object) -> dict[str, object]:
    return {
        "id": argument_id,
        "premise_statement_ids": premises,
        "conclusion_statement_id": conclusion,
        "inference_ids": [f"INF-{argument_id}"],
        "meaning": argument_id,
        **extra,
    }


def result(result_id: str) -> dict[str, object]:
    return {"id": result_id, "argument_id": result_id}


def relation(subject_kind: str, subject: str, predicate: str, obj: str, **extra: object) -> dict[str, object]:
    return {
        "id": f"REL-{subject}-{predicate}-{obj}",
        "subject_kind": subject_kind,
        "subject_id": subject,
        "predicate": predicate,
        "object_kind": "statement",
        "object_id": obj,
        **extra,
    }


def strengthens(strong: str, weak: str, result_id: str = "ARG-S-W") -> dict[str, object]:
    return relation("statement", strong, "strengthens", weak, verification_result_id=result_id, note="sibling versions")


# ROOT <= ARG-ROOT(WEAK, OTHER); STRONG <= ARG-STRONG(BASE); ARG-S-W: STRONG ⊢ WEAK.
STATEMENTS = [
    statement("ROOT"),
    statement("STRONG"),
    statement("WEAK"),
    statement("BASE"),
    statement("OTHER"),
    statement("ALT-OTHER"),
    statement("ALT-BASE"),
]
REGISTRATION = argument("ARG-S-W", ["STRONG"], "WEAK")
ARGUMENTS = [
    REGISTRATION,
    argument("ARG-ROOT", ["WEAK", "OTHER"], "ROOT"),
    argument("ARG-STRONG", ["BASE"], "STRONG"),
]
RESULTS = [result("ARG-S-W"), result("ARG-ROOT"), result("ARG-STRONG")]
SELF_EVIDENT = {"basis": "common_ground", "owner_approval": {"decision": "x", "date": "2026-11-05"}, "disagreement": "none recorded"}


def report(statements=STATEMENTS, arguments=ARGUMENTS, results=RESULTS, relations=(), root="ROOT"):
    return corpus.frontier_report(list(statements), list(arguments), list(results), list(relations), root=root)


def with_floor(*statement_ids: str) -> list[dict[str, object]]:
    return [
        statement(item["id"], self_evident=SELF_EVIDENT) if item["id"] in statement_ids else item
        for item in STATEMENTS
    ]


class StrengthPropagationTest(unittest.TestCase):
    def test_established_strong_establishes_weak(self) -> None:
        relations = [strengthens("STRONG", "WEAK")]
        rep = report(with_floor("STRONG"), relations=relations)
        self.assertIn("WEAK", rep["established_statements"])
        self.assertEqual(rep["closed_statements"]["WEAK"], "via_strength")
        (entry,) = rep["strength_order"]
        self.assertTrue(entry["weak_established_via_strength"])
        self.assertFalse(entry["strong_refuted_via_strength"])
        self.assertIn("STRONG => WEAK (ARG-S-W) [weak established via strength]", corpus.format_frontier(rep))

    def test_closed_but_unestablished_strong_does_not_close_weak(self) -> None:
        # STRONG is proved from the open BASE: closed, not established. The
        # registration argument does not close WEAK by rule (a).
        rep = report(relations=[strengthens("STRONG", "WEAK")])
        self.assertIn("STRONG", rep["closed_statements"])
        self.assertNotIn("WEAK", rep["closed_statements"])
        self.assertIn("WEAK", [item["statement_id"] for item in rep["items"]])
        # Reach and route expansion follow the registration like any verified
        # derivation (2026-11-12): STRONG reaches the root, and the route
        # expands WEAK through STRONG to STRONG's own open premise BASE.
        self.assertIn("STRONG", rep["reaching_root_statements"])
        self.assertEqual(rep["routes"]["routes"][0]["open_premise_statement_ids"], ["BASE", "OTHER"])
        # The same argument without the registration is an ordinary proof and
        # closes WEAK by rule (a); the registration only keeps that closure out.
        plain = report()
        self.assertIn("WEAK", plain["closed_statements"])
        for field in ["reaching_root_statements", "routes"]:
            self.assertEqual(rep[field], plain[field], field)

    def test_excluded_registration_preserves_declared_display_over_heuristic(self) -> None:
        results = [{**entry, "transcription": "assembly"} if entry["id"] == "ARG-S-W" else entry for entry in RESULTS]
        flag = {"result_id": "ARG-S-W", "argument_id": "ARG-S-W", "proof_steps": 1,
                "single_application_of": "hStrong", "goal_consequent_premises": []}
        rep = corpus.frontier_report(STATEMENTS, ARGUMENTS, results, [strengthens("STRONG", "WEAK")],
                                     root="ROOT", transcription=[flag])
        self.assertEqual(rep["transcription_results"]["ARG-S-W"], {"kind": "assembly", "declared": True})
        self.assertEqual(rep["transcription_flags"], [flag])
        # Displaying the registration must not restore it as a rule-(d) proof:
        # STRONG is closed from open BASE, so that would wrongly close WEAK.
        self.assertIn("STRONG", rep["closed_statements"])
        self.assertNotIn("WEAK", rep["closed_statements"])
        # A transcription registration is walked but, like every
        # transcription, never expands a route leaf.
        self.assertIn("STRONG", rep["reaching_root_statements"])
        self.assertEqual(rep["routes"]["routes"][0]["open_premise_statement_ids"], ["OTHER", "WEAK"])

    def test_excluded_registration_without_heuristic_retains_declared_kind(self) -> None:
        for kind in sorted(corpus.TRANSCRIPTION_KINDS):
            with self.subTest(kind=kind):
                results = [{**entry, "transcription": kind} if entry["id"] == "ARG-S-W" else entry for entry in RESULTS]
                actual = report(results=results, relations=[strengthens("STRONG", "WEAK")])
                baseline = report(relations=[strengthens("STRONG", "WEAK")])
                self.assertEqual(actual["transcription_results"]["ARG-S-W"], {"kind": kind, "declared": True})
                # Routes differ: a transcription registration expands nothing.
                for field in ["closed_statements", "established_statements", "strength_order", "items", "reaching_root_statements"]:
                    self.assertEqual(actual[field], baseline[field], field)
                established = report(with_floor("STRONG"), results=results, relations=[strengthens("STRONG", "WEAK")])
                self.assertEqual(established["closed_statements"]["WEAK"], "via_strength")

    def test_sibling_cycle_closes_nothing(self) -> None:
        # The mandate-scope shape: STRONG is proved from WEAK (and OTHER),
        # and WEAK is registered as entailed by STRONG. Neither closes the other.
        arguments = [REGISTRATION, argument("ARG-ROOT", ["STRONG"], "ROOT"), argument("ARG-STRONG", ["WEAK", "OTHER"], "STRONG")]
        rep = report(arguments=arguments, relations=[strengthens("STRONG", "WEAK")])
        self.assertIn("STRONG", rep["closed_statements"])
        self.assertNotIn("WEAK", rep["closed_statements"])
        self.assertEqual(rep["established_statements"], [])

    def test_refuted_weak_refutes_strong(self) -> None:
        # STRONG is an alternative to OTHER; refuting WEAK refutes STRONG by
        # contraposition, so OTHER is defended.
        arguments = [*ARGUMENTS, argument("ARG-NOT-WEAK", [], "ALT-BASE")]
        results = [*RESULTS, result("ARG-NOT-WEAK")]
        relations = [
            strengthens("STRONG", "WEAK"),
            relation("statement", "STRONG", "alternative_to", "OTHER"),
            relation("argument", "ARG-NOT-WEAK", "refutes", "WEAK"),
        ]
        rep = report(arguments=arguments, results=results, relations=relations)
        self.assertEqual(rep["refuted_statements"], ["STRONG", "WEAK"])
        self.assertIn("OTHER", rep["established_statements"])
        self.assertEqual(rep["closed_statements"]["OTHER"], "alternatives_refuted")
        self.assertTrue(rep["strength_order"][0]["strong_refuted_via_strength"])

    def test_propagation_never_runs_in_reverse(self) -> None:
        # Regression (#1017): an established weak version does not establish
        # the strong one, and a refuted strong version does not refute the
        # weak one.
        relations = [strengthens("STRONG", "WEAK")]
        rep = report(with_floor("WEAK"), relations=relations)
        self.assertIn("WEAK", rep["established_statements"])
        self.assertNotIn("STRONG", rep["established_statements"])

        arguments = [*ARGUMENTS, argument("ARG-NOT-STRONG", [], "ALT-BASE")]
        results = [*RESULTS, result("ARG-NOT-STRONG")]
        relations = [
            strengthens("STRONG", "WEAK"),
            relation("statement", "WEAK", "alternative_to", "OTHER"),
            relation("argument", "ARG-NOT-STRONG", "refutes", "STRONG"),
        ]
        rep = report(arguments=arguments, results=results, relations=relations)
        self.assertEqual(rep["refuted_statements"], ["STRONG"])
        self.assertNotIn("OTHER", rep["established_statements"])
        self.assertFalse(rep["strength_order"][0]["strong_refuted_via_strength"])

    def test_propagation_is_part_of_the_least_fixpoint(self) -> None:
        # The refutation of WEAK rests on OTHER, which is defended only once
        # STRONG (its alternative) is refuted, which needs WEAK refuted: a
        # circle, so nothing counts.
        arguments = [*ARGUMENTS, argument("ARG-NOT-WEAK", ["OTHER"], "ALT-BASE")]
        results = [*RESULTS, result("ARG-NOT-WEAK")]
        relations = [
            strengthens("STRONG", "WEAK"),
            relation("statement", "STRONG", "alternative_to", "OTHER"),
            relation("argument", "ARG-NOT-WEAK", "refutes", "WEAK"),
        ]
        rep = report(arguments=arguments, results=results, relations=relations)
        self.assertEqual(rep["refuted_statements"], [])
        self.assertNotIn("OTHER", rep["established_statements"])

    def test_attribution_stays_per_version(self) -> None:
        # A claim stating only the weak version leaves the strong one bare.
        claims = [{"id": "CLAIM-WEAK", "statement_id": "WEAK"}]
        arguments = [REGISTRATION, argument("ARG-ROOT", ["WEAK", "STRONG"], "ROOT")]
        rep = corpus.frontier_report(
            STATEMENTS, arguments, [result("ARG-S-W"), result("ARG-ROOT")], [strengthens("STRONG", "WEAK")],
            root="ROOT", claims=claims,
        )
        items = {item["statement_id"]: item for item in rep["items"]}
        self.assertEqual(items["WEAK"]["depth"], corpus.FRONTIER_STATED)
        self.assertEqual(items["STRONG"]["depth"], corpus.FRONTIER_BARE)
        self.assertEqual(items["STRONG"]["stating_claims"], [])

    def test_unbacked_relation_propagates_nothing(self) -> None:
        relations = [strengthens("STRONG", "WEAK", result_id="ARG-ROOT")]
        arguments = [argument("ARG-ROOT", ["WEAK", "OTHER"], "ROOT"), argument("ARG-STRONG", ["BASE"], "STRONG")]
        rep = report(with_floor("STRONG"), arguments=arguments, results=RESULTS[1:], relations=relations)
        self.assertEqual(rep["strength_order"], [])
        self.assertNotIn("WEAK", rep["established_statements"])


class StrengthValidationTest(unittest.TestCase):
    path = corpus.ROOT / "corpus/relations/test.json"
    results = {item["id"]: item for item in [*RESULTS, result("ARG-MODEL")]}
    arguments = {item["id"]: item for item in [*ARGUMENTS, argument("ARG-MODEL", [], "ALT-BASE")]}

    def validate(self, relation_record: dict[str, object]) -> None:
        corpus.validate_premise_program_relation(self.path, relation_record)
        corpus.validate_strength_registration(self.path, relation_record, self.results, self.arguments)

    def test_accepts_a_backed_registration_with_optional_strictness(self) -> None:
        self.validate(strengthens("STRONG", "WEAK"))
        self.validate({**strengthens("STRONG", "WEAK"), "strictness_result_id": "ARG-MODEL"})

    def test_rejects_a_registration_without_a_proved_entailment(self) -> None:
        for bad in (
            {k: v for k, v in strengthens("STRONG", "WEAK").items() if k != "verification_result_id"},
            strengthens("STRONG", "WEAK", result_id="UNKNOWN"),
            strengthens("STRONG", "WEAK", result_id="ARG-ROOT"),
            strengthens("WEAK", "STRONG"),
            strengthens("STRONG", "STRONG"),
            {**strengthens("STRONG", "WEAK"), "note": " "},
            {**strengthens("STRONG", "WEAK"), "strictness_result_id": "ARG-STRONG"},
            {**strengthens("STRONG", "WEAK"), "object_kind": "claim"},
        ):
            with self.subTest(relation=bad), self.assertRaises(corpus.CorpusError):
                self.validate(bad)

    def test_rejects_duplicate_or_reverse_pairs(self) -> None:
        pair = (self.path, strengthens("STRONG", "WEAK"))
        reverse = (self.path, {**strengthens("WEAK", "STRONG", result_id="OTHER"), "id": "REL-Z"})
        duplicate = (self.path, {**strengthens("STRONG", "WEAK", result_id="OTHER"), "id": "REL-Z"})
        shared = (self.path, {**strengthens("STRONG", "OTHER"), "id": "REL-Z"})
        corpus.validate_strength_order([pair])
        for extra in (reverse, duplicate, shared):
            with self.subTest(extra=extra[1]), self.assertRaises(corpus.CorpusError):
                corpus.validate_strength_order([pair, extra])

    def test_strong_version_needed_names_a_strong_premise_with_a_reason(self) -> None:
        path = corpus.ROOT / "corpus/arguments/test.json"
        ok = argument("ARG", ["STRONG"], "ROOT", strong_version_needed={"STRONG": "the weak version gives less"})
        corpus.validate_strong_version_needed(path, ok, {"STRONG"})
        for needed in ({}, {"STRONG": ""}, {"OTHER": "x"}, ["STRONG"]):
            bad = argument("ARG", ["STRONG", "OTHER"], "ROOT", strong_version_needed=needed)
            with self.subTest(needed=needed), self.assertRaises(corpus.CorpusError):
                corpus.validate_strong_version_needed(path, bad, {"STRONG"})

    def test_advisory_warning_for_a_strong_version_used_without_declaration(self) -> None:
        order = corpus.strength_order([strengthens("STRONG", "WEAK")], RESULTS, ARGUMENTS)
        users = [argument("ARG-A", ["STRONG"], "ROOT"), argument("ARG-B", ["STRONG"], "ROOT", strong_version_needed={"STRONG": "needed"})]
        (warning,) = corpus.strength_use_warnings([REGISTRATION, *users], order)
        self.assertIn("STRONG: used by 1 argument(s)", warning)
        self.assertIn("ARG-A", warning)
        self.assertNotIn("ARG-B", warning)
        self.assertNotIn("ARG-S-W", warning)

    def test_weakening_field_needs_one_premise(self) -> None:
        path = corpus.ROOT / "corpus/arguments/test.json"
        corpus.validate_weakening(path, argument("ARG", ["STRONG"], "WEAK", weakening=True))
        corpus.validate_weakening(path, argument("ARG", ["STRONG", "OTHER"], "WEAK"))
        for bad in (argument("ARG", ["STRONG"], "WEAK", weakening=False),
                    argument("ARG", ["STRONG", "OTHER"], "WEAK", weakening=True)):
            with self.subTest(bad=bad), self.assertRaises(corpus.CorpusError):
                corpus.validate_weakening(path, bad)

    def test_unregistered_weakening_is_flagged_from_explicit_fields(self) -> None:
        declared = {**REGISTRATION, "weakening": True}
        comparison = {**relation("statement", "BASE", "strength_comparison", "STRONG"),
                      "evidence_result_ids": {"implication": "ARG-STRONG"}}
        arguments = [declared, *ARGUMENTS[1:]]
        # Neither registered: the declared weakening and the comparison's implication are flagged.
        warnings = corpus.unregistered_weakening_warnings(arguments, RESULTS, [comparison], [])
        self.assertEqual(len(warnings), 2)
        self.assertIn("ARG-S-W: declares weakening from STRONG to WEAK", warnings[0])
        self.assertIn("ARG-STRONG: is the implication of strength_comparison", warnings[1])
        # Registering the pairs clears them; an unmarked one-premise argument is never flagged.
        relations = [comparison, strengthens("STRONG", "WEAK"), strengthens("BASE", "STRONG", result_id="ARG-STRONG")]
        order = corpus.strength_order(relations, RESULTS, arguments)
        self.assertEqual(corpus.unregistered_weakening_warnings(arguments, RESULTS, relations, order), [])
        self.assertEqual(corpus.unregistered_weakening_warnings(ARGUMENTS, RESULTS, [], []), [])

    def test_delta_forward_of_a_comparison_is_flagged(self) -> None:
        later = {**relation("statement", "BASE", "strength_comparison", "STRONG"),
                 "id": "REL-Z", "evidence_result_ids": {"delta_forward": "ARG-STRONG"}}
        earlier = {**later, "id": "REL-A"}
        warnings = corpus.unregistered_weakening_warnings(ARGUMENTS, RESULTS, [later, earlier], [])
        # The lowest relation id is named, as in Rust.
        self.assertEqual(len(warnings), 1)
        self.assertIn("ARG-STRONG: is the delta_forward of strength_comparison REL-A from BASE to STRONG", warnings[0])


class StrengthCorpusTest(unittest.TestCase):
    def test_registered_pairs_resolve(self) -> None:
        relations = [record for _, record in corpus.load_dir("relations")]
        results = [record for _, record in corpus.load_dir("results")]
        arguments = [record for _, record in corpus.load_dir("arguments")]
        registered = [relation for relation in relations if relation["predicate"] == corpus.STRENGTHENS_PREDICATE]
        order = corpus.strength_order(relations, results, arguments)
        self.assertEqual(len(order), len(registered))
        pairs = {(entry["strong_statement_id"], entry["weak_statement_id"]) for entry in order}
        self.assertIn(
            (legacy_uuid("statement", "STMT-MEANINGFULNESS-CLOSED-UNDER-NEGATION-STRONG"), legacy_uuid("statement", "STMT-MEANINGFULNESS-CLOSED-UNDER-NEGATION-WEAK")),
            pairs,
        )


if __name__ == "__main__":
    unittest.main()
