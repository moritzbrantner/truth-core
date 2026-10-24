#!/usr/bin/env python3
"""Tests for `corpus.py frontier` (issue #156). Run with:

    python3 -m unittest discover -s scripts -p 'test_*.py'
"""

from __future__ import annotations

import contextlib
import io
import json
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import corpus  # noqa: E402


def statement(statement_id: str, **extra: object) -> dict[str, object]:
    return {"id": statement_id, "paraphrase": statement_id.lower(), **extra}


def argument(argument_id: str, premises: list[str], conclusion: str) -> dict[str, object]:
    return {
        "id": argument_id,
        "premise_statement_ids": premises,
        "conclusion_statement_id": conclusion,
        "inference_ids": [f"INF-{argument_id}"],
        "meaning": argument_id,
    }


def relation(subject_kind: str, subject: str, predicate: str, obj: str) -> dict[str, object]:
    return {
        "id": f"REL-{subject}-{predicate}-{obj}",
        "subject_kind": subject_kind,
        "subject_id": subject,
        "predicate": predicate,
        "object_kind": "statement",
        "object_id": obj,
    }


# ROOT <= ARG-ROOT(MID, OPEN-B); MID <= ARG-MID(OPEN-A, SELF) verified;
# VERIFIED <= ARG-V() verified and used by ARG-ROOT-2; SIDE is off the root path.
STATEMENTS = [
    statement("ROOT"),
    statement("MID"),
    statement("OPEN-A"),
    statement("OPEN-B"),
    statement("SELF", self_evident={"justification_ids": ["CLAIM-SELF"]}),
    statement("SIDE"),
    statement("SIDE-CONCLUSION"),
]
ARGUMENTS = [
    argument("ARG-MID", ["OPEN-A", "SELF"], "MID"),
    argument("ARG-ROOT", ["MID", "OPEN-B"], "ROOT"),
    argument("ARG-SIDE", ["SIDE"], "SIDE-CONCLUSION"),
]
RESULTS = [{"id": "ARG-MID", "argument_id": "ARG-MID"}, {"id": "ARG-ROOT", "argument_id": "ARG-ROOT"}]


class FrontierReportTest(unittest.TestCase):
    def report(self, relations: list[dict[str, object]] | None = None, root: str = "ROOT"):
        return corpus.frontier_report(STATEMENTS, ARGUMENTS, RESULTS, relations or [], root=root)

    def ids(self, report: dict[str, object]) -> list[str]:
        return [item["statement_id"] for item in report["items"]]

    def test_excludes_verified_conclusions_and_self_evident_premises(self) -> None:
        report = self.report()
        self.assertNotIn("MID", self.ids(report))
        self.assertNotIn("SELF", self.ids(report))
        self.assertEqual(self.ids(report), ["OPEN-A", "OPEN-B", "SIDE"])

    def test_orders_by_root_reach_then_dependents(self) -> None:
        items = {item["statement_id"]: item for item in self.report()["items"]}
        self.assertEqual(items["OPEN-A"]["transitive_dependent_arguments"], ["ARG-MID", "ARG-ROOT"])
        self.assertEqual(items["OPEN-A"]["path_to_root"], ["OPEN-A", "ARG-MID", "MID", "ARG-ROOT", "ROOT"])
        self.assertEqual(items["OPEN-B"]["dependent_arguments"], ["ARG-ROOT"])
        self.assertIsNone(items["SIDE"]["path_to_root"])

    def test_transcription_only_conclusion_stays_open(self) -> None:
        flag = {
            "result_id": "ARG-MID",
            "argument_id": "ARG-MID",
            "proof_steps": 1,
            "single_application_of": "hBridge",
            "goal_consequent_premises": [],
        }
        report = corpus.frontier_report(STATEMENTS, ARGUMENTS, RESULTS, [], root="ROOT", transcription=[flag])
        items = {item["statement_id"]: item for item in report["items"]}
        self.assertTrue(items["MID"]["transcription_only"])
        self.assertIn("open although proved", corpus.format_frontier(report))
        # A short proof that is not a single application still closes the node.
        flag["single_application_of"] = None
        report = corpus.frontier_report(STATEMENTS, ARGUMENTS, RESULTS, [], root="ROOT", transcription=[flag])
        self.assertNotIn("MID", self.ids(report))

    def test_reports_missing_alternatives(self) -> None:
        report = self.report()
        self.assertFalse(report["alternatives_recorded"])
        self.assertIn("alternatives: no alternatives recorded", corpus.format_frontier(report))

    def test_alternatives_must_all_be_refuted_by_verified_arguments(self) -> None:
        relations = [
            relation("statement", "ALT-1", "alternative_to", "OPEN-A"),
            relation("statement", "ALT-2", "alternative_to", "OPEN-A"),
            relation("argument", "ARG-MID", "refutes", "ALT-1"),
        ]
        items = {item["statement_id"]: item for item in self.report(relations)["items"]}
        self.assertEqual(
            items["OPEN-A"]["alternatives"],
            [{"statement_id": "ALT-1", "refuted": True}, {"statement_id": "ALT-2", "refuted": False}],
        )
        # An unverified argument does not refute.
        relations.append(relation("argument", "ARG-SIDE", "refutes", "ALT-2"))
        self.assertIn("OPEN-A", self.ids(self.report(relations)))
        relations.append(relation("argument", "ARG-ROOT", "refutes", "ALT-2"))
        self.assertNotIn("OPEN-A", self.ids(self.report(relations)))

    def test_lists_attacking_objections(self) -> None:
        relations = [relation("argument", "ARG-OBJECTION", "attacks", "OPEN-B")]
        report = self.report(relations)
        items = {item["statement_id"]: item for item in report["items"]}
        self.assertEqual(items["OPEN-B"]["objections"], ["argument:ARG-OBJECTION"])
        self.assertIn("objections: argument:ARG-OBJECTION", corpus.format_frontier(report))

    def test_output_is_deterministic(self) -> None:
        shuffled = corpus.frontier_report(
            list(reversed(STATEMENTS)), list(reversed(ARGUMENTS)), list(reversed(RESULTS)), [], root="ROOT"
        )
        self.assertEqual(shuffled, self.report())


class FrontierSchemaTest(unittest.TestCase):
    def test_self_evident_requires_a_known_justification(self) -> None:
        path = corpus.ROOT / "corpus" / "statements" / "example.json"
        corpus.validate_self_evident(path, statement("X"), set(), set())
        corpus.validate_self_evident(
            path, statement("X", self_evident={"justification_ids": ["R"]}), set(), {"R"}
        )
        for marking in (True, {"justification_ids": []}, {"justification_ids": ["UNKNOWN"]}):
            with self.assertRaises(corpus.CorpusError):
                corpus.validate_self_evident(path, statement("X", self_evident=marking), {"C"}, {"R"})

    def test_premise_program_relations_have_fixed_kinds(self) -> None:
        path = corpus.ROOT / "corpus" / "relations" / "example.json"
        corpus.validate_premise_program_relation(path, relation("argument", "A", "refutes", "S"))
        corpus.validate_premise_program_relation(path, relation("source", "A", "related_to", "S"))
        with self.assertRaises(corpus.CorpusError):
            corpus.validate_premise_program_relation(path, relation("statement", "A", "refutes", "S"))


class TranscriptionHeuristicTest(unittest.TestCase):
    def test_consequent_after_unfolding_and_quantifiers(self) -> None:
        definitions = {"Bridge": (["a", "b", "c"], "a ∧ b → c"), "Goal": (["c"], "c")}
        self.assertEqual(corpus.consequent(corpus.unfold_once("Bridge P Q R", definitions)), "R")
        self.assertEqual(corpus.consequent("∀ x, A x → (B x → C x)"), "B x → C x")
        self.assertEqual(corpus.strip_quantifier_prefix(corpus.unfold_once("Goal R", definitions)), "R")
        self.assertIsNone(corpus.consequent("A ∧ (B → C)"))

    def test_flags_known_transcription_and_spares_the_skeleton(self) -> None:
        records = {name: [record for _, record in corpus.load_dir(name)] for name in ("results", "arguments", "statements")}
        flags = {
            flag["result_id"]: flag
            for flag in corpus.transcription_flags(records["results"], records["arguments"], records["statements"])
        }
        teleology = flags["ARIST-PHYS-198B-199A-NATURAL-TELEOLOGY"]
        self.assertEqual(teleology["single_application_of"], "hBridge")
        self.assertEqual(
            teleology["goal_consequent_premises"],
            [{"hypothesis": "hBridge", "statement_ids": ["STMT-NATURAL-REGULARITY-IMPLIES-TELEOLOGY"]}],
        )
        for result_id in ("CATHOLICISM-SKELETON", "CATHOLICISM-STAGE1-FROM-PRIMA-VIA", "AQUINAS-ST-I-Q2-A3-PRIMA-VIA"):
            self.assertNotIn(result_id, flags)


class FrontierCorpusTest(unittest.TestCase):
    """Runs the command against the real corpus."""

    def run_frontier(self, *args: str) -> str:
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            status = corpus.main_with(["frontier", *args])
        self.assertEqual(status, 0)
        return output.getvalue()

    def test_skeleton_premises_are_open_and_reach_the_root(self) -> None:
        report = json.loads(self.run_frontier("--json", "--reaching-root"))
        self.assertTrue(report["root_known"])
        ids = {item["statement_id"] for item in report["items"]}
        self.assertIn("STMT-BRIDGE-CHRISTS-CHURCH-FOUNDED-BY-GOD", ids)
        self.assertIn("STMT-UNIQUE-PURE-ACT-FIRST-MOVER-IS-GOD", ids)
        # Stage 1 and the prima via conclusion are conclusions of verified results.
        self.assertNotIn("STMT-GOD-EXISTS", ids)
        self.assertNotIn("STMT-FIRST-UNMOVED-MOVER-CANNOT-BE-LACKING", ids)
        self.assertTrue(all(item["path_to_root"][-1] == "STMT-CATHOLICISM-TRUE" for item in report["items"]))

    def test_excluded_middle_instances_are_closed(self) -> None:
        # #167: both root-path instances are closed through the self-evident
        # general principle; their instantiation results stay transcriptions.
        report = json.loads(self.run_frontier("--json"))
        ids = {item["statement_id"] for item in report["items"]}
        for statement_id in (
            "STMT-EXCLUDED-MIDDLE",
            "STMT-FIRST-UNMOVED-MOVER-EXISTS-OR-NOT",
            "STMT-FIRST-UNMOVED-MOVERS-IDENTICAL-OR-DISTINCT",
        ):
            self.assertNotIn(statement_id, ids)
        self.assertTrue(report["alternatives_recorded"])
        single = {
            flag["result_id"] for flag in report["transcription_flags"] if flag["single_application_of"]
        }
        self.assertIn("CATHOLICISM-FIRST-UNMOVED-MOVER-EXISTS-OR-NOT-FROM-EM", single)
        self.assertNotIn("LOGIC-EXCLUDED-MIDDLE-IRREFUTABLE", single)

    def test_text_output_is_stable(self) -> None:
        self.assertEqual(self.run_frontier(), self.run_frontier())


if __name__ == "__main__":
    unittest.main()
