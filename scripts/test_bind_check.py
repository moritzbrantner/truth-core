"""Offline tests for `corpus.py bind-check` (#162), on synthetic Lean descriptions."""

from __future__ import annotations

import unittest
from pathlib import Path

import corpus

NS = "TruthCore.Test."


def statements(**declarations: str | None) -> dict:
    index = {}
    for statement_id, declaration in declarations.items():
        record = {"id": statement_id, "paraphrase": statement_id}
        if declaration is not None:
            record["lean_declaration"] = NS + declaration
        index[statement_id] = (Path(f"{statement_id}.json"), record)
    return index


def hyp(name: str, head: str | None, *, prop: bool = True, type_: str | None = None) -> dict:
    logical = {"Not", "Exists", "And", "Or", "Iff"}
    full = None if head is None else (head if head in logical else NS + head)
    return {"name": name, "prop": prop, "head": full, "type": type_ or (full or "?")}


def param(name: str, type_: str = "Type") -> dict:
    return {"name": name, "prop": False, "head": None, "type": type_}


RESULT = {"id": "R", "theorem": "TruthCore.Results.Test.thm"}
ARGUMENT = {"premise_statement_ids": ["P", "Q"], "conclusion_statement_id": "C"}
STATEMENTS = statements(P="PReading", Q="QReading", C="CReading", E=None)


def describe(binders: list[dict], result: dict) -> dict:
    return {"theorem": RESULT["theorem"], "binders": binders, "result": result}


class BindResultTest(unittest.TestCase):
    def bind(self, binders, result, argument=ARGUMENT, index=STATEMENTS):
        return corpus.bind_result(RESULT, argument, index, describe(binders, result))

    def test_vocabulary_parameters_are_not_premises(self):
        report = self.bind(
            [
                param("Being"),
                param("Respect", "Sort u"),
                param("MovedIn", "Being → Respect → Prop"),
                param("A", "Prop"),
                hyp("hQ", "QReading"),
                hyp("hP", "PReading"),
            ],
            hyp("", "CReading"),
        )
        self.assertEqual(report["status"], "bound")
        self.assertEqual(report["parameters"], ["Being", "Respect", "MovedIn", "A"])
        self.assertEqual(
            [(entry["hypothesis"], entry["statement_id"]) for entry in report["premises"]],
            [("hQ", "Q"), ("hP", "P")],
        )

    def test_unrecorded_hypothesis_is_reported(self):
        report = self.bind(
            [hyp("hP", "PReading"), hyp("hQ", "QReading"), hyp("hX", "XReading")],
            hyp("", "CReading"),
        )
        self.assertEqual(report["status"], "mismatch")
        self.assertEqual([p["kind"] for p in report["problems"]], ["extra-hypothesis"])
        self.assertEqual(report["problems"][0]["hypothesis"], "hX")

    def test_recorded_premise_missing_from_theorem(self):
        report = self.bind([hyp("hP", "PReading")], hyp("", "CReading"))
        self.assertEqual(report["problems"], [
            {"kind": "missing-premise", "statement_id": "Q", "lean_declaration": NS + "QReading"}
        ])

    def test_conclusion_mismatch(self):
        report = self.bind([hyp("hP", "PReading"), hyp("hQ", "QReading")], hyp("", "PReading"))
        self.assertEqual([p["kind"] for p in report["problems"]], ["conclusion-mismatch"])

    def test_negated_hypothesis_does_not_bind_to_its_operand(self):
        report = self.bind(
            [hyp("hP", "PReading"), hyp("hQ", "Not", type_="¬TruthCore.Test.QReading")],
            hyp("", "CReading"),
        )
        self.assertEqual(
            sorted(p["kind"] for p in report["problems"]), ["extra-hypothesis", "missing-premise"]
        )

    def bind_undeclared(self, pins, type_="∃ x, Causes x cosmos", premises=("P", "Q")):
        argument = {"premise_statement_ids": list(premises), "conclusion_statement_id": "E"}
        return corpus.bind_result(
            RESULT,
            argument,
            STATEMENTS,
            describe([hyp("hP", "PReading"), hyp("hQ", "QReading")], hyp("", "Exists", type_=type_)),
            pins,
        )

    def test_pinned_logical_form_conclusion_passes(self):
        report = self.bind_undeclared({("R", "conclusion", "E"): "∃ x,\n  Causes x cosmos"})
        self.assertEqual(report["status"], "pinned")
        self.assertEqual(report["undecidable"][0]["role"], "conclusion")

    def test_unpinned_logical_form_conclusion_fails(self):
        report = self.bind_undeclared({})
        self.assertEqual(report["status"], "mismatch")
        self.assertEqual([p["kind"] for p in report["problems"]], ["undeclared-binding"])

    def test_pin_with_a_different_type_fails(self):
        report = self.bind_undeclared({("R", "conclusion", "E"): "∃ x, x ≠ cosmos"})
        self.assertEqual(report["status"], "mismatch")

    def test_undeclared_premise_needs_a_pin(self):
        argument = {"premise_statement_ids": ["P", "E"], "conclusion_statement_id": "C"}
        report = self.bind(
            [hyp("hP", "PReading"), hyp("hX", "Exists", type_="∃ x, F x")], hyp("", "CReading"), argument
        )
        self.assertEqual([p["kind"] for p in report["problems"]], ["undeclared-binding"])

    def test_undeclared_statement_cannot_hide_a_corpus_declaration(self):
        argument = {"premise_statement_ids": ["P", "E"], "conclusion_statement_id": "E"}
        report = self.bind([hyp("hP", "PReading"), hyp("hQ", "QReading")], hyp("", "CReading"), argument)
        self.assertEqual(
            [p["kind"] for p in report["problems"]],
            ["extra-hypothesis", "missing-premise", "conclusion-unbound-declaration"],
        )

    def test_lean_error_is_a_mismatch(self):
        report = corpus.bind_result(RESULT, ARGUMENT, STATEMENTS, {"theorem": "x", "error": "unknown constant"})
        self.assertEqual(report["status"], "mismatch")


def bundle(name: str, head: str, conjuncts: list[dict]) -> dict:
    return dict(hyp(name, head), bundle=conjuncts)


class TheoryBundleTest(unittest.TestCase):
    """A theory hypothesis is unfolded one step and its conjuncts bind exactly."""

    INDEX = statements(P="PReading", Q="QReading", R="RReading", C="CReading", K="KConsistent", E=None)

    def bind(self, binders, result, premises=("P", "Q", "R"), commitments=None):
        argument = {"premise_statement_ids": list(premises), "conclusion_statement_id": "C"}
        if commitments is not None:
            argument["commitment_statement_ids"] = list(commitments)
            argument["conclusion_statement_id"] = "K"
        return corpus.bind_result(RESULT, argument, self.INDEX, describe(binders, result), {})

    def test_bundle_conjuncts_cover_premises(self):
        report = self.bind(
            [param("s", "Sig"), bundle("hT", "Theory", [hyp("", "PReading"), hyp("", "QReading")]), hyp("hR", "RReading")],
            hyp("", "CReading"),
        )
        self.assertEqual(report["status"], "bound")
        self.assertEqual(
            [(entry["hypothesis"], entry["statement_id"]) for entry in report["premises"]],
            [("hT.1", "P"), ("hT.2", "Q"), ("hR", "R")],
        )

    def test_bundle_missing_a_listed_premise(self):
        report = self.bind([bundle("hT", "Theory", [hyp("", "PReading"), hyp("", "QReading")])], hyp("", "CReading"))
        self.assertEqual([p["kind"] for p in report["problems"]], ["missing-premise"])

    def test_bundle_with_an_extra_conjunct(self):
        report = self.bind(
            [bundle("hT", "Theory", [hyp("", "PReading"), hyp("", "QReading"), hyp("", "RReading"), hyp("", "XReading")])],
            hyp("", "CReading"),
        )
        self.assertEqual([p["kind"] for p in report["problems"]], ["unbound-bundle-conjunct"])

    def test_nested_theory_conjunct_is_not_unfolded(self):
        report = self.bind(
            [bundle("hT", "Theory", [hyp("", "PReading"), hyp("", "Grounding")]), hyp("hR", "RReading")],
            hyp("", "CReading"),
            premises=("P", "R"),
        )
        self.assertEqual([p["kind"] for p in report["problems"]], ["unbound-bundle-conjunct"])

    def test_logical_form_conjunct_cannot_be_pinned(self):
        report = self.bind(
            [bundle("hT", "Theory", [hyp("", "PReading"), hyp("", "Exists", type_="∃ x, F x")])],
            hyp("", "CReading"),
            premises=("P", "E"),
        )
        self.assertEqual(report["status"], "mismatch")
        self.assertIn("unbound-bundle-conjunct", [p["kind"] for p in report["problems"]])

    def test_unfold_failure_is_a_mismatch(self):
        report = self.bind([dict(hyp("hT", "Theory"), bundle="cannot unfold")], hyp("", "CReading"), premises=())
        self.assertEqual([p["kind"] for p in report["problems"]], ["bundle-unfold-failed"])

    def test_consistency_commitments_bind_exactly(self):
        result = dict(hyp("", "KConsistent"), bundle=[hyp("", "PReading"), hyp("", "QReading")])
        report = self.bind([], result, premises=(), commitments=("P", "Q"))
        self.assertEqual(report["status"], "bound")
        self.assertEqual([c["statement_id"] for c in report["commitments"]], ["P", "Q"])

    def test_consistency_commitment_missing_or_extra(self):
        result = dict(hyp("", "KConsistent"), bundle=[hyp("", "PReading"), hyp("", "XReading")])
        report = self.bind([], result, premises=(), commitments=("P", "Q"))
        self.assertEqual(
            sorted(p["kind"] for p in report["problems"]), ["missing-commitment", "unbound-commitment"]
        )

    def test_theory_conclusion_needs_recorded_commitments(self):
        result = dict(hyp("", "KConsistent"), bundle=[hyp("", "PReading"), hyp("", "XReading")])
        argument = {"premise_statement_ids": ["P", "Q", "R"], "conclusion_statement_id": "K"}
        report = corpus.bind_result(
            RESULT,
            argument,
            self.INDEX,
            describe([hyp("hP", "PReading"), hyp("hQ", "QReading"), hyp("hR", "RReading")], result),
            {},
        )
        self.assertEqual([p["kind"] for p in report["problems"]], ["theory-conclusion-without-commitments"])

    def test_commitments_need_a_theory_conclusion(self):
        report = self.bind([], hyp("", "KConsistent"), premises=(), commitments=("P",))
        self.assertEqual([p["kind"] for p in report["problems"]], ["commitments-without-bundle"])


class BindToolInputTest(unittest.TestCase):
    def test_input_is_sorted_and_deduplicated(self):
        results = [
            (Path("b.json"), {"id": "B", "solution_module": "M2", "theorem": "t2"}),
            (Path("a.json"), {"id": "A", "solution_module": "M2", "theorem": "t1"}),
            (Path("c.json"), {"id": "C", "solution_module": "M1", "theorem": "t3"}),
        ]
        self.assertEqual(
            corpus.bind_tool_input(results),
            {
                "modules": ["M1", "M2"],
                "theorems": ["t1", "t2", "t3"],
                "bundle_prefixes": corpus.THEORY_BUNDLE_PREFIXES,
            },
        )


if __name__ == "__main__":
    unittest.main()
