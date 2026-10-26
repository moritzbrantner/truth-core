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
        self.assertNotIn("SIDE", report["reaching_root_statements"])

    def test_reaching_root_statements_match_item_paths(self) -> None:
        # The explorer's root-reachability filter (#491) reads this list; it must
        # agree with `path_to_root` for every open premise, routed or not.
        arguments = [*ARGUMENTS, argument("ARG-ROOT-2", ["SIDE"], "ROOT")]
        for relations in ([], [relation("argument", "ARG-ROOT", "root_route", "ROOT")]):
            report = corpus.frontier_report(STATEMENTS, arguments, RESULTS, relations, root="ROOT")
            reaching = set(report["reaching_root_statements"])
            for item in report["items"]:
                self.assertEqual(item["path_to_root"] is not None, item["statement_id"] in reaching)
        self.assertEqual(
            self.report()["reaching_root_statements"], ["MID", "OPEN-A", "OPEN-B", "ROOT", "SELF"]
        )
        self.assertEqual(self.report(root="ABSENT")["reaching_root_statements"], [])

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
        arguments = [*ARGUMENTS, argument("ARG-FREE-1", [], "NOT-ALT-1"), argument("ARG-FREE-2", [], "NOT-ALT-2")]
        results = [*RESULTS, {"id": "ARG-FREE-1", "argument_id": "ARG-FREE-1"}]
        relations = [
            relation("statement", "ALT-1", "alternative_to", "OPEN-A"),
            relation("statement", "ALT-2", "alternative_to", "OPEN-A"),
            relation("argument", "ARG-FREE-1", "refutes", "ALT-1"),
        ]

        def report(relations, results=results):
            return corpus.frontier_report(STATEMENTS, arguments, results, relations, root="ROOT")

        items = {item["statement_id"]: item for item in report(relations)["items"]}
        self.assertEqual(
            items["OPEN-A"]["alternatives"],
            [{"statement_id": "ALT-1", "refuted": True}, {"statement_id": "ALT-2", "refuted": False}],
        )
        # An unverified argument does not refute.
        relations.append(relation("argument", "ARG-FREE-2", "refutes", "ALT-2"))
        self.assertIn("OPEN-A", self.ids(report(relations)))
        results = [*results, {"id": "ARG-FREE-2", "argument_id": "ARG-FREE-2"}]
        self.assertNotIn("OPEN-A", self.ids(report(relations, results)))
        self.assertEqual(report(relations, results)["closed_statements"]["OPEN-A"], "alternatives_refuted")

    def test_refutation_counts_only_from_closed_premises(self) -> None:
        # #391: ARG-MID is verified but rests on the open OPEN-A, so its
        # refutation of OPEN-B's only alternative does not defend OPEN-B.
        relations = [
            relation("statement", "ALT", "alternative_to", "OPEN-B"),
            relation("argument", "ARG-MID", "refutes", "ALT"),
        ]
        report = self.report(relations)
        self.assertIn("OPEN-B", self.ids(report))
        self.assertEqual(
            report["refutations"],
            [
                {
                    "relation_id": "REL-ARG-MID-refutes-ALT",
                    "argument_id": "ARG-MID",
                    "statement_id": "ALT",
                    "verified": True,
                    "open_premise_statement_ids": ["OPEN-A"],
                    "counted": False,
                }
            ],
        )
        self.assertEqual(report["refuted_statements"], [])
        self.assertIn("refutations not counted for rule (c): 1", corpus.format_frontier(report))
        # Fixpoint: once OPEN-A is defended, ARG-MID's refutation counts too.
        relations += [
            relation("statement", "ALT-A", "alternative_to", "OPEN-A"),
            relation("argument", "ARG-FREE", "refutes", "ALT-A"),
        ]
        arguments = [*ARGUMENTS, argument("ARG-FREE", [], "NOT-ALT-A")]
        results = [*RESULTS, {"id": "ARG-FREE", "argument_id": "ARG-FREE"}]
        report = corpus.frontier_report(STATEMENTS, arguments, results, relations, root="ROOT")
        self.assertEqual(report["refuted_statements"], ["ALT", "ALT-A"])
        self.assertNotIn("OPEN-A", self.ids(report))
        self.assertNotIn("OPEN-B", self.ids(report))
        self.assertTrue(all(refutation["counted"] for refutation in report["refutations"]))

    def test_declared_transcription_is_not_proved(self) -> None:
        # #391: an opaque-atom result declared in its record closes nothing by
        # itself, like a single application; rule (d) still applies.
        results = [{"id": "ARG-MID", "argument_id": "ARG-MID", "transcription": "opaque_atoms"}, RESULTS[1]]
        report = corpus.frontier_report(STATEMENTS, ARGUMENTS, results, [], root="ROOT")
        items = {item["statement_id"]: item for item in report["items"]}
        self.assertTrue(items["MID"]["transcription_only"])
        self.assertNotIn("MID", report["closed_statements"])
        self.assertEqual(report["transcription_results"], {"ARG-MID": {"kind": "opaque_atoms", "declared": True}})
        statements = [
            {**record, "self_evident": {"justification_ids": ["CLAIM-A"]}} if record["id"] == "OPEN-A" else record
            for record in STATEMENTS
        ]
        report = corpus.frontier_report(statements, ARGUMENTS, results, [], root="ROOT")
        self.assertEqual(report["closed_statements"]["MID"], "via_transcription")

    def test_q3a4_conditional_result_keeps_causal_premises_open(self) -> None:
        root = "STMT-DISTINCT-ESSE-REQUIRES-EXTERNAL-CAUSE"
        result = json.loads((corpus.ROOT / "corpus/results/Q3A4-DISTINCT-ESSE-EXTERNAL-CAUSE.json").read_text())
        argument_record = json.loads((corpus.ROOT / "corpus/arguments/Q3A4-DISTINCT-ESSE-EXTERNAL-CAUSE.json").read_text())
        premises = argument_record["premise_statement_ids"]
        statements = [statement(sid) for sid in [root, *premises]]
        report = corpus.frontier_report(statements, [argument_record], [result], [], root=root)
        self.assertNotIn(root, report["closed_statements"])
        self.assertTrue(set(premises).issubset(self.ids(report)))
        self.assertTrue(report["transcription_results"][result["id"]]["declared"])

    def test_assembly_flag_is_a_transcription(self) -> None:
        # #391: pure conjunction assembly counts like a single application.
        flag = {
            "result_id": "ARG-MID",
            "argument_id": "ARG-MID",
            "proof_steps": 1,
            "single_application_of": None,
            "assembly_of": ["hA", "hSelf"],
            "opaque_atoms": False,
            "goal_consequent_premises": [],
        }
        report = corpus.frontier_report(STATEMENTS, ARGUMENTS, RESULTS, [], root="ROOT", transcription=[flag])
        self.assertIn("MID", self.ids(report))
        self.assertEqual(report["transcription_results"], {"ARG-MID": {"kind": "assembly", "declared": False}})
        self.assertIn("assembly of hA, hSelf", corpus.format_frontier(report))
        # The opaque-atom heuristic alone only warns.
        flag["assembly_of"] = None
        flag["opaque_atoms"] = True
        report = corpus.frontier_report(STATEMENTS, ARGUMENTS, RESULTS, [], root="ROOT", transcription=[flag])
        self.assertNotIn("MID", self.ids(report))
        self.assertEqual(report["transcription_results"], {})

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


class RouteCostTest(unittest.TestCase):
    """`frontier --routes` (#391, owner decision 2026-10-26, corrected): a
    sourced or bare premise may stand as one open leaf; an intermediate
    conclusion is expanded into the union of its premises' leaves under its
    cheapest verified non-transcription proof; a route costs the size of the
    union over its premises."""

    STATEMENTS = [
        statement("ROOT"),
        statement("A"),
        statement("B"),
        statement("C"),
        statement("P1"),
        statement("P2"),
        statement("SE", self_evident={"justification_ids": ["CLAIM-SE"]}),
    ]

    def routes(self, arguments, results, relations=(), transcription=None, claims=None):
        report = corpus.frontier_report(
            self.STATEMENTS,
            arguments,
            results,
            list(relations),
            root="ROOT",
            transcription=transcription,
            claims=claims,
        )
        return report["routes"]

    def by_id(self, routes):
        return {entry["argument_id"]: entry for entry in routes["routes"]}

    def test_costs_and_cheapest_route(self) -> None:
        arguments = [
            argument("R1", ["A", "B", "SE"], "ROOT"),
            argument("R2", ["C"], "ROOT"),
            argument("R3", ["P1"], "ROOT"),
        ]
        results = [{"id": "R1", "argument_id": "R1"}, {"id": "R2", "argument_id": "R2"}]
        routes = self.routes(arguments, results, [relation("argument", "R1", "root_route", "ROOT")])
        entries = self.by_id(routes)
        self.assertEqual(entries["R1"]["cost"], 2)
        self.assertEqual(entries["R1"]["open_premise_statement_ids"], ["A", "B"])
        self.assertTrue(entries["R1"]["designated"])
        self.assertEqual(entries["R2"]["cost"], 1)
        self.assertTrue(entries["R2"]["cheapest"])
        self.assertFalse(entries["R3"]["verified"])
        self.assertFalse(entries["R3"]["cheapest"])
        self.assertEqual(routes["cheapest_argument_id"], "R2")
        self.assertEqual([entry["argument_id"] for entry in routes["routes"]], ["R2", "R1", "R3"])
        text = corpus.format_routes(routes)
        self.assertIn("cheapest R2", text)
        self.assertIn("   2         3  R1  [designated]", text)
        self.assertIn("   1         1  R2  [cheapest]", text)

    def test_added_derivation_under_a_sourced_premise_never_raises_a_route_cost(self) -> None:
        arguments = [argument("R1", ["A", "B"], "ROOT")]
        results = [{"id": "R1", "argument_id": "R1"}]
        claims = [{"id": "CLAIM-A", "statement_id": "A"}]
        base = self.by_id(self.routes(arguments, results, claims=claims))["R1"]["cost"]
        self.assertEqual(base, 2)
        # A verified derivation of the sourced A from two open premises: A
        # may still stand as one leaf.
        widened = [*arguments, argument("DA", ["P1", "P2"], "A")]
        widened_results = [*results, {"id": "DA", "argument_id": "DA"}]
        entry = self.by_id(self.routes(widened, widened_results, claims=claims))["R1"]
        self.assertEqual(entry["cost"], 2)
        self.assertEqual(entry["proved_unestablished_statement_ids"], ["A"])
        # A supports relation makes a premise sourced too.
        supported = [relation("claim", "CLAIM-A", "supports", "A")]
        self.assertEqual(self.by_id(self.routes(widened, widened_results, supported))["R1"]["cost"], 2)
        # A derivation of B from the self-evident SE lowers the cost.
        grounded = [*arguments, argument("DB", ["SE"], "B")]
        entry = self.by_id(self.routes(grounded, [*results, {"id": "DB", "argument_id": "DB"}]))["R1"]
        self.assertEqual(entry["cost"], 1)

    def test_intermediate_conclusions_are_expanded(self) -> None:
        # A has no claim and is concluded by verified proofs: it is expanded
        # under its cheapest proof (DA2: {P1}), and leaves shared between
        # premises count once.
        arguments = [
            argument("R1", ["A", "B"], "ROOT"),
            argument("DA", ["P1", "P2"], "A"),
            argument("DA2", ["P1"], "A"),
            argument("DB", ["P1", "SE"], "B"),
        ]
        results = [{"id": rid, "argument_id": rid} for rid in ("R1", "DA", "DA2", "DB")]
        entry = self.by_id(self.routes(arguments, results))["R1"]
        self.assertEqual(entry["open_premise_statement_ids"], ["P1"])
        self.assertEqual(entry["cost"], 1)
        # Only the more expensive proof: A expands to {P1, P2}.
        arguments, results = arguments[:2] + arguments[3:], results[:2] + results[3:]
        self.assertEqual(self.by_id(self.routes(arguments, results))["R1"]["open_premise_statement_ids"], ["P1", "P2"])

    def test_transcriptions_and_cycles_lower_no_cost(self) -> None:
        arguments = [
            argument("R1", ["A"], "ROOT"),
            argument("TA", ["P1"], "A"),
            argument("CA", ["B"], "A"),
            argument("CB", ["A"], "B"),
        ]
        results = [{"id": rid, "argument_id": rid} for rid in ("R1", "CA", "CB")]
        results.append({"id": "TA", "argument_id": "TA", "transcription": "opaque_atoms"})
        self.assertEqual(self.by_id(self.routes(arguments, results))["R1"]["cost"], 1)
        # A transcription from closed premises carries cost 0 (rule (d)).
        arguments[1] = argument("TA", ["SE"], "A")
        self.assertEqual(self.by_id(self.routes(arguments, results))["R1"]["cost"], 0)


class FrontierSchemaTest(unittest.TestCase):
    def test_transcription_field_is_validated(self) -> None:
        corpus.validate_result_transcription("r.json", {"transcription": "opaque_atoms"})
        corpus.validate_result_transcription("r.json", {"description": "Derived, not a transcription."})
        with self.assertRaises(corpus.CorpusError):
            corpus.validate_result_transcription("r.json", {"transcription": "maybe"})
        for description in ("Opaque-atom transcription (invariant 16): …", "Transcription: …", "Near-transcription"):
            with self.assertRaises(corpus.CorpusError):
                corpus.validate_result_transcription("r.json", {"description": description})

    def test_self_evident_requires_a_known_justification(self) -> None:
        path = corpus.ROOT / "corpus" / "statements" / "example.json"
        corpus.validate_self_evident(path, statement("X"), set(), set())
        corpus.validate_self_evident(
            path,
            statement("STMT-EXCLUDED-MIDDLE", self_evident={"justification_ids": ["R"], "disagreement": "none recorded"}),
            set(),
            {"R"},
        )
        for marking in (True, {"justification_ids": []}, {"justification_ids": ["UNKNOWN"]}):
            with self.assertRaises(corpus.CorpusError):
                corpus.validate_self_evident(path, statement("X", self_evident=marking), {"C"}, {"R"})

    def test_self_evident_basis_shapes(self) -> None:
        path = corpus.ROOT / "corpus" / "statements" / "example.json"
        known = {"P", "Q", "RIVAL", "NOT-P"}

        def check(marking: dict[str, object]) -> None:
            corpus.validate_self_evident(path, statement("P", self_evident=marking), {"C", "D"}, {"R"}, known)

        none = {"disagreement": "none recorded"}
        check({"basis": "retorsion", "justification_ids": ["R"], "denial_statement_id": "NOT-P", **none})
        check({
            "basis": "common_ground",
            "justification_ids": ["C", "D"],
            "question_statement_id": "Q",
            "positions": [{"statement_id": "Q", "claim_ids": ["C"]}, {"statement_id": "RIVAL", "claim_ids": ["D"]}],
        })
        check({
            "basis": "observation",
            "justification_ids": ["C"],
            "sceptical_rival_ids": ["NOT-P"],
            "disagreement": {"rival_statement_ids": ["NOT-P"], "claim_ids": ["D"]},
        })
        for marking in (
            {"justification_ids": ["R"], **none},  # basis-less outside the legacy list
            {"basis": "logical", "justification_ids": ["R"], **none},
            {"basis": "retorsion", "justification_ids": ["C"], "denial_statement_id": "NOT-P", **none},
            {"basis": "retorsion", "justification_ids": ["R"], "denial_statement_id": "UNKNOWN", **none},
            # #378: a disagreement record is required, and must name known rivals or claims.
            {"basis": "retorsion", "justification_ids": ["R"], "denial_statement_id": "NOT-P"},
            {"basis": "retorsion", "justification_ids": ["R"], "denial_statement_id": "NOT-P", "disagreement": {}},
            {"basis": "retorsion", "justification_ids": ["R"], "denial_statement_id": "NOT-P", "disagreement": "none"},
            {
                "basis": "retorsion",
                "justification_ids": ["R"],
                "denial_statement_id": "NOT-P",
                "disagreement": {"rival_statement_ids": ["UNKNOWN"]},
            },
            {"basis": "common_ground", "justification_ids": ["C"], "question_statement_id": "Q", "positions": []},
            {
                "basis": "common_ground",
                "justification_ids": ["C", "D"],
                "question_statement_id": "Q",
                "positions": [{"statement_id": "Q", "claim_ids": ["C"]}],
            },
            {"basis": "observation", "justification_ids": ["R"], **none},
        ):
            with self.subTest(marking=marking), self.assertRaises(corpus.CorpusError):
                check(marking)

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


class FloorBasisTest(unittest.TestCase):
    """#500: a self_evident marking closes only while its basis criterion holds."""

    def report(self, statements, arguments=(), results=(), relations=(), claims=(), root="ROOT"):
        return corpus.frontier_report(
            [statement("ROOT"), *statements],
            [argument("ARG-ROOT", ["P"], "ROOT"), *arguments],
            [{"id": "ARG-ROOT", "argument_id": "ARG-ROOT"}, *results],
            list(relations),
            root=root,
            claims=[{"id": claim_id, "statement_id": sid} for claim_id, sid in claims],
        )

    def floor(self, report):
        return {entry["statement_id"]: entry for entry in report["floor"]}

    COMMON_GROUND = {
        "basis": "common_ground",
        "justification_ids": ["C-THEIST", "C-NATURALIST"],
        "question_statement_id": "THEISM",
        "positions": [
            {"statement_id": "THEISM", "claim_ids": ["C-THEIST"]},
            {"statement_id": "NATURALISM", "claim_ids": ["C-NATURALIST"]},
        ],
    }
    COMMON_CLAIMS = [("C-THEIST", "P"), ("C-NATURALIST", "P")]
    QUESTION = [relation("statement", "NATURALISM", "alternative_to", "THEISM")]

    def test_common_ground_closes_relative_to_recorded_rivals(self) -> None:
        statements = [statement("P", self_evident=self.COMMON_GROUND), statement("THEISM"), statement("NATURALISM")]
        report = self.report(statements, relations=self.QUESTION, claims=self.COMMON_CLAIMS)
        self.assertEqual(report["closed_statements"]["P"], "self_evident")
        self.assertTrue(self.floor(report)["P"]["met"])
        self.assertEqual(report["routes"]["floor_bases"], [{"statement_id": "P", "basis": "common_ground"}])
        self.assertIn("closed relative to floor bases: P (common_ground)", corpus.format_routes(report["routes"]))

    def test_new_rival_reopens_common_ground(self) -> None:
        statements = [
            statement("P", self_evident=self.COMMON_GROUND),
            statement("THEISM"),
            statement("NATURALISM"),
            statement("NIHILISM"),
            statement("NOT-P"),
        ]
        # A new rival position on the question without a proponent claim.
        report = self.report(
            statements,
            relations=[*self.QUESTION, relation("statement", "NIHILISM", "alternative_to", "THEISM")],
            claims=self.COMMON_CLAIMS,
        )
        self.assertIn("P", [item["statement_id"] for item in report["items"]])
        self.assertIn("NIHILISM", self.floor(report)["P"]["reasons"][0])
        # A rival denying the premise itself.
        report = self.report(
            statements,
            relations=[*self.QUESTION, relation("statement", "NOT-P", "alternative_to", "P")],
            claims=self.COMMON_CLAIMS,
        )
        self.assertNotIn("P", report["closed_statements"])
        item = next(item for item in report["items"] if item["statement_id"] == "P")
        self.assertEqual(item["floor_unmet"]["basis"], "common_ground")
        self.assertIn("self_evident basis common_ground not met", corpus.format_frontier(report))
        self.assertEqual(report["routes"]["floor_bases"], [])
        # No rival recorded on the question at all.
        report = self.report(statements, claims=self.COMMON_CLAIMS)
        self.assertFalse(self.floor(report)["P"]["met"])
        # A claim that does not state the premise is no commitment.
        report = self.report(statements, relations=self.QUESTION, claims=[("C-THEIST", "P"), ("C-NATURALIST", "Q")])
        self.assertIn("NATURALISM", self.floor(report)["P"]["reasons"][0])

    def test_retorsion_needs_a_counted_non_transcription_refutation_of_the_denial(self) -> None:
        marking = {"basis": "retorsion", "justification_ids": ["RET"], "denial_statement_id": "NOT-P"}
        statements = [statement("P", self_evident=marking), statement("NOT-P"), statement("PRESUP")]
        relations = [
            relation("statement", "NOT-P", "alternative_to", "P"),
            relation("argument", "ARG-RET", "refutes", "NOT-P"),
        ]
        ret = [argument("ARG-RET", ["PRESUP"], "NOT-NOT-P")]
        results = [{"id": "RET", "argument_id": "ARG-RET"}]
        report = self.report(statements, ret, results, relations)
        self.assertEqual(self.floor(report)["P"]["reasons"], ["RET rests on open premises PRESUP"])
        self.assertNotIn("P", report["closed_statements"])
        # Once the presupposition is closed, the retorsion closes the premise.
        closed_presup = [statement("P", self_evident=marking), statement("NOT-P"), statement("PRESUP")]
        report = self.report(
            closed_presup,
            [*ret, argument("ARG-PRESUP", [], "PRESUP")],
            [*results, {"id": "PRESUP-R", "argument_id": "ARG-PRESUP"}],
            relations,
        )
        self.assertEqual(report["closed_statements"]["P"], "self_evident")
        # A circular retorsion (resting on P itself) closes nothing.
        report = self.report(statements, [argument("ARG-RET", ["P"], "NOT-NOT-P")], results, relations)
        self.assertFalse(self.floor(report)["P"]["met"])
        # A declared transcription does not count.
        report = self.report(
            closed_presup,
            [argument("ARG-RET", [], "NOT-NOT-P")],
            [{"id": "RET", "argument_id": "ARG-RET", "transcription": "assembly"}],
            relations,
        )
        self.assertEqual(self.floor(report)["P"]["reasons"], ["RET is a transcription"])

    def test_observation_needs_a_stating_claim_and_handled_sceptical_rivals(self) -> None:
        marking = {"basis": "observation", "justification_ids": ["C-OBS"], "sceptical_rival_ids": ["ELEATIC"]}
        statements = [statement("P", self_evident=marking), statement("ELEATIC")]
        rival = [relation("statement", "ELEATIC", "alternative_to", "P")]
        report = self.report(statements, relations=rival, claims=[("C-OBS", "P")])
        self.assertEqual(self.floor(report)["P"]["reasons"], ["sceptical rivals not refuted: ELEATIC"])
        refutation = [*rival, relation("argument", "ARG-ELEA", "refutes", "ELEATIC")]
        report = self.report(
            statements,
            [argument("ARG-ELEA", [], "NOT-ELEATIC")],
            [{"id": "ELEA", "argument_id": "ARG-ELEA"}],
            refutation,
            claims=[("C-OBS", "P")],
        )
        self.assertEqual(report["closed_statements"]["P"], "self_evident")
        # A rival not recorded as global scepticism reopens it.
        statements.append(statement("PHYSICALIST"))
        report = self.report(
            statements,
            [argument("ARG-ELEA", [], "NOT-ELEATIC")],
            [{"id": "ELEA", "argument_id": "ARG-ELEA"}],
            [*refutation, relation("statement", "PHYSICALIST", "alternative_to", "P")],
            claims=[("C-OBS", "P")],
        )
        self.assertEqual(
            self.floor(report)["P"]["reasons"],
            ["rivals not recorded as global sceptical positions: PHYSICALIST"],
        )

    def test_stale_disagreement_record_reopens_the_marking(self) -> None:
        marking = {"justification_ids": ["C"], "disagreement": {"rival_statement_ids": ["OLD"]}}
        statements = [statement("P", self_evident=marking), statement("OLD"), statement("NEW")]
        rivals = [relation("statement", "OLD", "alternative_to", "P")]
        self.assertTrue(self.floor(self.report(statements, relations=rivals))["P"]["met"])
        report = self.report(statements, relations=[*rivals, relation("statement", "NEW", "alternative_to", "P")])
        self.assertEqual(self.floor(report)["P"]["reasons"], ["disagreement record omits recorded rivals: NEW"])
        self.assertNotIn("P", report["closed_statements"])

    def test_legacy_marking_closes_and_is_listed(self) -> None:
        report = self.report([statement("P", self_evident={"justification_ids": ["C"]})])
        self.assertEqual(report["floor"][0]["basis"], "legacy")
        self.assertIn("floor: 1 of 1 self_evident markings meet their basis", corpus.format_frontier(report))


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


class AssemblyAndOpaqueHeuristicTest(unittest.TestCase):
    def test_assembly_of_hypotheses(self) -> None:
        names = {"s", "hClaims", "hRose", "hA"}
        self.assertEqual(corpus.assembly_of(["⟨hClaims, hRose⟩"], names), ["hClaims", "hRose"])
        self.assertEqual(corpus.assembly_of(["exact ⟨hClaims, ⟨hRose, hA.1⟩⟩"], names), ["hClaims", "hRose", "hA"])
        self.assertEqual(corpus.assembly_of(["And.intro hClaims hRose"], names), ["hClaims", "hRose"])
        self.assertEqual(
            corpus.assembly_of(["constructor", "· exact hClaims", "· exact hRose"], names), ["hClaims", "hRose"]
        )
        self.assertEqual(
            corpus.assembly_of(["obtain ⟨hX, hY⟩ := hA", "exact ⟨hY, hX⟩"], names), ["hY", "hX"]
        )
        for steps in (
            ["⟨hClaims, f hRose⟩"],
            ["⟨hClaims, other⟩"],
            ["exact hClaims"],
            ["⟨hClaims⟩"],
            ["constructor", "· exact hClaims", "· simp"],
            ["obtain ⟨hX, hY⟩ := lemma hA", "exact ⟨hY, hX⟩"],
        ):
            self.assertIsNone(corpus.assembly_of(steps, names), steps)

    def test_opaque_atoms(self) -> None:
        definitions = {
            "Bridge": (["a", "b", "c"], "a ∧ b → ¬ c"),
            "Goal": (["c"], "¬ c"),
            "Typed": (["x"], "Moves x ∧ Being x"),
        }
        groups, rest = corpus.binder_groups("(A B C : Prop) (hScope : A ∧ B) (hBridge : Bridge A B C) : Goal C")
        self.assertTrue(corpus.opaque_atoms(groups, rest[1:].strip(), definitions))
        groups, rest = corpus.binder_groups("(A : Prop) (x : Thing) (h : Typed x) : A")
        self.assertFalse(corpus.opaque_atoms(groups, rest[1:].strip(), definitions))
        groups, rest = corpus.binder_groups("(A : Prop) (h : A) : Typed y")
        self.assertFalse(corpus.opaque_atoms(groups, rest[1:].strip(), definitions))
        # No hypotheses: a theorem of logic over a Prop parameter is not flagged.
        groups, rest = corpus.binder_groups("(p : Prop) : ¬¬(p ∨ ¬p)")
        self.assertFalse(corpus.opaque_atoms(groups, rest[1:].strip(), definitions))


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
        # #145: the prima via's regress premise is derived from the secunda via's.
        self.assertNotIn("STMT-NO-INFINITE-PER-SE-MOVER-SERIES", depths)
        # #367: the finite-ancestry route expanded efficient-cause regress
        # into three bare premises. The finite-branching bridge now further
        # expands ancestry into two explicit, still-open hypotheses. This
        # refines the argument without establishing its metaphysical premises.
        self.assertNotIn("STMT-NO-INFINITE-PER-SE-EFFICIENT-CAUSE-SERIES", depths)
        self.assertNotIn("STMT-FINITE-DISTINCT-CAUSAL-ANCESTRY", depths)
        for premise in (
            "STMT-CAUSAL-FINITE-IMMEDIATE-PREDECESSORS",
            "STMT-CAUSAL-WELL-FOUNDED-PREDECESSORS",
            "STMT-CAUSAL-HISTORY-HAS-NO-LOOPS",
            "STMT-PER-SE-LINKS-IN-FINITE-HISTORY-RELATION",
        ):
            self.assertEqual(depths[premise], "bare")
        claims = {record["id"]: record for _, record in corpus.load_dir("claims")}
        self.assertEqual(
            claims["AQUINAS-ST-I-Q46-A2-AD7-NO-INFINITE-EFFICIENT-CAUSES-A"]["statement_id"],
            "STMT-NO-INFINITE-PER-SE-EFFICIENT-CAUSE-SERIES",
        )

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

    def test_opaque_atom_results_are_declared_and_not_proved(self) -> None:
        # #391: audit B (#388) found opaque-atom transcriptions counted as
        # proved; each now declares its kind and none closes by rule (a).
        report = json.loads(self.run_frontier("--json"))
        results = {record["id"]: record for _, record in corpus.load_dir("results")}
        arguments = {record["id"]: record for _, record in corpus.load_dir("arguments")}
        opaque = [flag["result_id"] for flag in report["transcription_flags"] if flag.get("opaque_atoms")]
        self.assertGreater(len(opaque), 50)
        for result_id in opaque:
            self.assertEqual(results[result_id].get("transcription"), "opaque_atoms", result_id)
        conclusion = arguments[results["ARIST-PHYS-245A-245B-NO-INTERMEDIATE-THREE-MOTIONS"]["argument_id"]][
            "conclusion_statement_id"
        ]
        self.assertNotEqual(report["closed_statements"].get(conclusion), "proved")
        self.assertEqual(
            report["transcription_results"]["HIDDENNESS-GAP-HAS-REASON"], {"kind": "instantiation", "declared": True}
        )

    def test_routes_cover_every_root_argument(self) -> None:
        routes = json.loads(self.run_frontier("--routes", "--json"))
        arguments = [record for _, record in corpus.load_dir("arguments")]
        self.assertEqual(
            sorted(entry["argument_id"] for entry in routes["routes"]),
            sorted(record["id"] for record in arguments if record["conclusion_statement_id"] == corpus.DEFAULT_FRONTIER_ROOT),
        )
        cheapest = [entry for entry in routes["routes"] if entry["cheapest"]]
        self.assertEqual([entry["argument_id"] for entry in cheapest], [routes["cheapest_argument_id"]])
        self.assertEqual(cheapest[0]["cost"], min(entry["cost"] for entry in routes["routes"] if entry["verified"]))
        self.assertIn("routes to STMT-CATHOLICISM-TRUE", self.run_frontier("--routes"))

    def test_skeleton_route_is_expanded_through_god_exists(self) -> None:
        # #391 correction: STMT-GOD-EXISTS is an intermediate conclusion with
        # no stating claim, so the skeleton route counts the open leaves
        # under its proof rather than one node.
        routes = json.loads(self.run_frontier("--routes", "--json"))
        skeleton = next(entry for entry in routes["routes"] if entry["argument_id"] == "CATHOLICISM-SKELETON")
        self.assertNotIn("STMT-GOD-EXISTS", skeleton["open_premise_statement_ids"])
        self.assertGreater(skeleton["cost"], skeleton["premise_count"])
        self.assertIn("STMT-NOTHING-IN-ACT-AND-POTENCY-IN-SAME-RESPECT", skeleton["open_premise_statement_ids"])
        self.assertEqual(skeleton["cost"], len(skeleton["open_premise_statement_ids"]))

    def test_text_output_is_stable(self) -> None:
        self.assertEqual(self.run_frontier(), self.run_frontier())


if __name__ == "__main__":
    unittest.main()
