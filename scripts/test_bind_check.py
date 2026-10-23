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


class BindToolInputTest(unittest.TestCase):
    def test_input_is_sorted_and_deduplicated(self):
        results = [
            (Path("b.json"), {"id": "B", "solution_module": "M2", "theorem": "t2"}),
            (Path("a.json"), {"id": "A", "solution_module": "M2", "theorem": "t1"}),
            (Path("c.json"), {"id": "C", "solution_module": "M1", "theorem": "t3"}),
        ]
        self.assertEqual(
            corpus.bind_tool_input(results), {"modules": ["M1", "M2"], "theorems": ["t1", "t2", "t3"]}
        )


if __name__ == "__main__":
    unittest.main()
