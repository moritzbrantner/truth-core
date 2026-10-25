#!/usr/bin/env python3
"""Tests for definition and disambiguation records (issue #204). Run with:

    python3 -m unittest discover -s scripts -p 'test_*.py'
"""

from __future__ import annotations

import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import corpus  # noqa: E402

DEFINITION_PATH = corpus.ROOT / "corpus" / "definitions" / "example.json"
DISAMBIGUATION_PATH = corpus.ROOT / "corpus" / "disambiguations" / "example.json"
LEAN = "def IsMaximumIn := True"


def definition(**fields: object) -> dict[str, object]:
    return {"id": "DEF-X", "term": "x", "definition": "what x means", **fields}


class DefinitionTest(unittest.TestCase):
    def test_sourced_definition_needs_known_claims(self) -> None:
        corpus.validate_definition(
            DEFINITION_PATH, definition(basis="sourced", claim_ids=["C"]), {"C"}, LEAN
        )
        for fields in ({}, {"claim_ids": []}, {"claim_ids": ["UNKNOWN"]}):
            with self.subTest(fields=fields), self.assertRaises(corpus.CorpusError):
                corpus.validate_definition(
                    DEFINITION_PATH, definition(basis="sourced", **fields), {"C"}, LEAN
                )

    def test_stipulative_definition_needs_a_note(self) -> None:
        corpus.validate_definition(
            DEFINITION_PATH, definition(basis="stipulative", note="why"), set(), LEAN
        )
        with self.assertRaises(corpus.CorpusError):
            corpus.validate_definition(DEFINITION_PATH, definition(basis="stipulative"), set(), LEAN)

    def test_rejects_unknown_basis_prefix_and_lean_declaration(self) -> None:
        bad = (
            definition(basis="obvious", note="n"),
            definition(id="X", basis="stipulative", note="n"),
            definition(basis="stipulative", note="n", lean_declaration="A.Missing"),
        )
        for record in bad:
            with self.subTest(record=record), self.assertRaises(corpus.CorpusError):
                corpus.validate_definition(DEFINITION_PATH, record, set(), LEAN)
        corpus.validate_definition(
            DEFINITION_PATH,
            definition(basis="stipulative", note="n", lean_declaration="A.IsMaximumIn"),
            set(),
            LEAN,
        )


class DisambiguationTest(unittest.TestCase):
    def test_needs_two_known_senses(self) -> None:
        record = {"id": "DISAMB-X", "term": "x", "resolution": "r", "sense_definition_ids": ["DEF-A", "DEF-B"]}
        corpus.validate_disambiguation(DISAMBIGUATION_PATH, record, {"DEF-A", "DEF-B"})
        for senses in (["DEF-A"], ["DEF-A", "DEF-A"], ["DEF-A", "DEF-UNKNOWN"]):
            with self.subTest(senses=senses), self.assertRaises(corpus.CorpusError):
                corpus.validate_disambiguation(
                    DISAMBIGUATION_PATH, {**record, "sense_definition_ids": senses}, {"DEF-A", "DEF-B"}
                )
        with self.assertRaises(corpus.CorpusError):
            corpus.validate_disambiguation(
                DISAMBIGUATION_PATH, {**record, "resolution": ""}, {"DEF-A", "DEF-B"}
            )


class ArgumentSensesTest(unittest.TestCase):
    def test_mixing_senses_requires_the_disambiguation(self) -> None:
        path = corpus.ROOT / "corpus" / "arguments" / "example.json"
        statements = {
            "S1": (path, {"id": "S1", "definition_ids": ["DEF-A"]}),
            "S2": (path, {"id": "S2", "definition_ids": ["DEF-B"]}),
        }
        disambiguations = [(path, {"id": "DISAMB-X", "term": "x", "sense_definition_ids": ["DEF-A", "DEF-B"]})]
        argument = {"conclusion_statement_id": "S2", "premise_statement_ids": ["S1"]}
        with self.assertRaises(corpus.CorpusError):
            corpus.validate_argument_senses(path, argument, statements, disambiguations)
        corpus.validate_argument_senses(path, {**argument, "disambiguation_ids": ["DISAMB-X"]}, statements, disambiguations)
        corpus.validate_argument_senses(path, {**argument, "premise_statement_ids": []}, statements, disambiguations)


class ProseIdTest(unittest.TestCase):
    def test_cited_ids_must_exist(self) -> None:
        record = {"resolution": "STMT-A is read as DEF-B (see DISAMB-C); AQUINAS-X is not checked."}
        corpus.validate_prose_ids(DISAMBIGUATION_PATH, record, ("resolution",), {"STMT-A", "DEF-B", "DISAMB-C"})
        with self.assertRaises(corpus.CorpusError):
            corpus.validate_prose_ids(DISAMBIGUATION_PATH, record, ("resolution",), {"STMT-A", "DEF-B"})


class TermLinkTest(unittest.TestCase):
    def test_links_must_resolve(self) -> None:
        path = corpus.ROOT / "corpus" / "statements" / "example.json"
        self.assertEqual(corpus.validate_term_links(path, {"id": "S"}, {"DEF-A"}, {"DISAMB-A"}), [])
        self.assertEqual(
            corpus.validate_term_links(
                path, {"definition_ids": ["DEF-A"], "disambiguation_ids": ["DISAMB-A"]}, {"DEF-A"}, {"DISAMB-A"}
            ),
            ["DEF-A"],
        )
        for record in (
            {"definition_ids": ["DEF-UNKNOWN"]},
            {"disambiguation_ids": ["DISAMB-UNKNOWN"]},
            {"definition_ids": []},
            {"definition_ids": "DEF-A"},
        ):
            with self.subTest(record=record), self.assertRaises(corpus.CorpusError):
                corpus.validate_term_links(path, record, {"DEF-A"}, {"DISAMB-A"})


if __name__ == "__main__":
    unittest.main()
