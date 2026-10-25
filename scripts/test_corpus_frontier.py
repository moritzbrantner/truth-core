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
PARITY_FIXTURE = Path(__file__).resolve().parent / "testdata" / "frontier-transcription-closure.json"


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

    def test_reports_why_each_closed_statement_is_closed(self) -> None:
        report = self.report()
        self.assertEqual(
            report["closed_statements"],
            {"MID": "proved", "ROOT": "proved", "SELF": "self_evident"},
        )
        # MID and ROOT are proved but rest on open premises, so only SELF is established.
        self.assertEqual(report["established_statements"], ["SELF"])

    def test_established_follows_verified_results_from_established_premises(self) -> None:
        statements = [
            {**record, "self_evident": {"justification_ids": ["CLAIM"]}} if record["id"] in {"OPEN-A", "OPEN-B"} else record
            for record in STATEMENTS
        ]
        report = corpus.frontier_report(statements, ARGUMENTS, RESULTS, [], root="ROOT")
        self.assertEqual(report["established_statements"], ["MID", "OPEN-A", "OPEN-B", "ROOT", "SELF"])

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

    def test_transcription_closes_conclusion_when_all_premises_are_closed(self) -> None:
        # Rule (d), #143 2026-10-24: MID is transcribed from OPEN-A and SELF;
        # it stays open while OPEN-A is open and closes once OPEN-A is closed.
        flag = {
            "result_id": "ARG-MID",
            "argument_id": "ARG-MID",
            "proof_steps": 1,
            "single_application_of": "hBridge",
            "goal_consequent_premises": [],
        }
        statements = [dict(record) for record in STATEMENTS]
        report = corpus.frontier_report(statements, ARGUMENTS, RESULTS, [], root="ROOT", transcription=[flag])
        self.assertIn("MID", self.ids(report))
        self.assertEqual(report["closed_via_transcription"], [])
        for record in statements:
            if record["id"] == "OPEN-A":
                record["self_evident"] = {"justification_ids": ["CLAIM-A"]}
        report = corpus.frontier_report(statements, ARGUMENTS, RESULTS, [], root="ROOT", transcription=[flag])
        self.assertNotIn("MID", self.ids(report))
        self.assertEqual(
            report["closed_via_transcription"],
            [
                {
                    "statement_id": "MID",
                    "result_id": "ARG-MID",
                    "argument_id": "ARG-MID",
                    "premise_statement_ids": ["OPEN-A", "SELF"],
                    "path_to_root": ["MID", "ARG-ROOT", "ROOT"],
                }
            ],
        )
        self.assertIn(
            "MID: closed via transcription ARG-MID from closed premises (OPEN-A, SELF)",
            corpus.format_frontier(report),
        )

    def test_root_route_admits_only_the_designated_argument(self) -> None:
        # #143, 2026-10-24: a second argument for ROOT from SIDE gives SIDE a
        # path to the root, until a root_route designates ARG-ROOT alone.
        arguments = [*ARGUMENTS, argument("ARG-ROOT-2", ["SIDE"], "ROOT")]
        report = corpus.frontier_report(STATEMENTS, arguments, RESULTS, [], root="ROOT")
        items = {item["statement_id"]: item for item in report["items"]}
        self.assertEqual(items["SIDE"]["path_to_root"], ["SIDE", "ARG-ROOT-2", "ROOT"])
        routed = [relation("argument", "ARG-ROOT", "root_route", "ROOT")]
        report = corpus.frontier_report(STATEMENTS, arguments, RESULTS, routed, root="ROOT")
        items = {item["statement_id"]: item for item in report["items"]}
        self.assertIsNone(items["SIDE"]["path_to_root"])
        self.assertEqual(items["SIDE"]["transitive_dependent_arguments"], ["ARG-ROOT-2", "ARG-SIDE"])
        self.assertEqual(items["OPEN-B"]["path_to_root"], ["OPEN-B", "ARG-ROOT", "ROOT"])

    def test_shared_parity_fixture(self) -> None:
        # Same fixture as apps/corpus-explorer/src/lib/proposition-graph.test.ts.
        fixture = json.loads(PARITY_FIXTURE.read_text(encoding="utf-8"))
        flags = [
            {
                "result_id": result_id,
                "argument_id": next(r["argument_id"] for r in fixture["results"] if r["id"] == result_id),
                "proof_steps": 1,
                "single_application_of": "hBridge",
                "goal_consequent_premises": [],
            }
            for result_id in fixture["transcription_result_ids"]
        ]
        for order in (1, -1):
            report = corpus.frontier_report(
                fixture["statements"][::order],
                fixture["arguments"][::order],
                fixture["results"][::order],
                fixture["relations"][::order],
                root="TOP",
                transcription=flags[::order],
                claims=fixture["claims"][::order],
            )
            self.assertEqual(sorted(self.ids(report)), fixture["expected_frontier"])
            self.assertEqual(
                {item["statement_id"]: item["depth"] for item in report["items"]}, fixture["expected_depth"]
            )
            self.assertEqual(
                {item["statement_id"]: item["result_id"] for item in report["closed_via_transcription"]},
                fixture["expected_closed_via_transcription"],
            )

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

    def test_lists_supporting_claims_without_closing(self) -> None:
        relations = [relation("claim", "CLAIM-EVIDENCE", "supports", "OPEN-B")]
        report = self.report(relations)
        items = {item["statement_id"]: item for item in report["items"]}
        self.assertEqual(items["OPEN-B"]["supporting_claims"], ["CLAIM-EVIDENCE"])
        self.assertIn("supporting source claims: CLAIM-EVIDENCE", corpus.format_frontier(report))

    def test_classifies_open_premises_by_depth(self) -> None:
        # #143 (2026-10-24): bare = no stating claim and no supports relation.
        claims = [{"id": "CLAIM-A", "statement_id": "OPEN-A"}]
        report = corpus.frontier_report(STATEMENTS, ARGUMENTS, RESULTS, [], root="ROOT", claims=claims)
        items = {item["statement_id"]: item for item in report["items"]}
        self.assertEqual(items["OPEN-A"]["depth"], "sourced")
        self.assertEqual(items["OPEN-A"]["stating_claims"], ["CLAIM-A"])
        self.assertEqual(items["OPEN-B"]["depth"], "bare")
        self.assertEqual(report["depth_counts"], {"bare": 2, "sourced": 1})
        self.assertIn("3 open premises: 2 bare, 1 sourced-undefended", corpus.format_frontier(report))
        supported = corpus.frontier_report(
            STATEMENTS,
            ARGUMENTS,
            RESULTS,
            [relation("claim", "CLAIM-EVIDENCE", "supports", "OPEN-B")],
            root="ROOT",
            claims=claims,
        )
        self.assertEqual(
            {item["statement_id"]: item["depth"] for item in supported["items"]},
            {"OPEN-A": "sourced", "OPEN-B": "sourced", "SIDE": "bare"},
        )

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
        corpus.validate_premise_program_relation(path, relation("claim", "C", "supports", "S"))
        with self.assertRaises(corpus.CorpusError):
            corpus.validate_premise_program_relation(path, relation("statement", "A", "supports", "S"))
        corpus.validate_premise_program_relation(path, relation("argument", "A", "root_route", "S"))
        with self.assertRaises(corpus.CorpusError):
            corpus.validate_premise_program_relation(path, relation("claim", "C", "root_route", "S"))


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
        # The designated root route (root_route, #143 2026-10-24) takes stage 1
        # through the fuller nominal definition, so the bare identification
        # premise of the other routes no longer reaches the root.
        self.assertIn("STMT-GOD-NAMES-THE-FULLY-DESCRIBED-PRINCIPLE", ids)
        self.assertNotIn("STMT-UNIQUE-PURE-ACT-FIRST-MOVER-IS-GOD", ids)
        # Stage 1 and the prima via conclusion are conclusions of verified results.
        self.assertNotIn("STMT-GOD-EXISTS", ids)
        self.assertNotIn("STMT-FIRST-UNMOVED-MOVER-CANNOT-BE-LACKING", ids)
        self.assertTrue(all(item["path_to_root"][-1] == "STMT-CATHOLICISM-TRUE" for item in report["items"]))
        # Depth counts cover exactly the premises that reach the root.
        counts = report["depth_counts"]
        self.assertEqual(counts["bare"] + counts["sourced"], report["open_premise_count"])
        depths = {item["statement_id"]: item["depth"] for item in report["items"]}
        self.assertEqual(depths["STMT-BRIDGE-CHRISTS-CHURCH-FOUNDED-BY-GOD"], "bare")
        self.assertEqual(depths["STMT-NO-INFINITE-PER-SE-MOVER-SERIES"], "sourced")

    def test_excluded_middle_instances_close_via_transcription(self) -> None:
        # #167: the instances are derived only by instantiating the
        # self-evident STMT-EXCLUDED-MIDDLE. Invariant 16 keeps the results
        # transcriptions, but rule (d) (#143, 2026-10-24) closes the instances
        # because their only premise is closed.
        report = json.loads(self.run_frontier("--json"))
        items = {item["statement_id"]: item for item in report["items"]}
        self.assertNotIn("STMT-EXCLUDED-MIDDLE", items)
        closures = {closure["statement_id"]: closure for closure in report["closed_via_transcription"]}
        for statement_id in (
            "STMT-FIRST-UNMOVED-MOVER-EXISTS-OR-NOT",
            "STMT-FIRST-UNMOVED-MOVERS-IDENTICAL-OR-DISTINCT",
        ):
            self.assertNotIn(statement_id, items)
            self.assertEqual(closures[statement_id]["premise_statement_ids"], ["STMT-EXCLUDED-MIDDLE"])
        self.assertTrue(report["alternatives_recorded"])
        single = {
            flag["result_id"] for flag in report["transcription_flags"] if flag["single_application_of"]
        }
        self.assertIn("CATHOLICISM-FIRST-UNMOVED-MOVER-EXISTS-OR-NOT-FROM-EM", single)
        self.assertNotIn("LOGIC-EXCLUDED-MIDDLE-IRREFUTABLE", single)

    def test_bridge_transcriptions_with_open_bridge_premises_stay_open(self) -> None:
        # An Aristotle "A ∧ B → C" bridge transcription must not close its
        # conclusion: its bridge premise is open, so rule (d) does not apply.
        report = json.loads(self.run_frontier("--json"))
        items = {item["statement_id"]: item for item in report["items"]}
        self.assertIn("STMT-NATURAL-REGULARITY-IMPLIES-TELEOLOGY", items)
        for statement_id in ("STMT-TIME-IS-NOT-MOTION", "STMT-NOTHING-MOVES-IN-NOW"):
            self.assertTrue(items[statement_id]["transcription_only"])
        closed = {closure["statement_id"] for closure in report["closed_via_transcription"]}
        flagged = {
            flag["argument_id"]
            for flag in report["transcription_flags"]
            if flag["single_application_of"] and flag["goal_consequent_premises"]
        }
        arguments = {record["id"]: record for _, record in corpus.load_dir("arguments")}
        checked = 0
        for argument_id in flagged:
            bridges = {
                statement_id
                for flag in report["transcription_flags"]
                if flag["argument_id"] == argument_id
                for premise in flag["goal_consequent_premises"]
                for statement_id in premise["statement_ids"]
            }
            if bridges & items.keys():
                checked += 1
                self.assertNotIn(arguments[argument_id]["conclusion_statement_id"], closed)
        self.assertGreater(checked, 10)

    def test_text_output_is_stable(self) -> None:
        self.assertEqual(self.run_frontier(), self.run_frontier())


if __name__ == "__main__":
    unittest.main()
