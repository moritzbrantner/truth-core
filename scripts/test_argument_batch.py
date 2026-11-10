#!/usr/bin/env python3
"""Tests for scripts/argument_batch.py (owner decision 2026-11-07)."""

from __future__ import annotations

import sys
import json
import tempfile
import uuid
from unittest.mock import patch
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import argument_batch  # noqa: E402

SOLUTION = """module

public import TruthCore.Foo

@[expose] public section

/-! A module docstring
that spans lines and mentions
end of things, section headings and theorem names. -/

namespace TruthCore.Results.Bar
open TruthCore.Foo

namespace Control
def witness : Prop := True
end Control

section Helpers
/-- Helper, omitted from the Challenge. -/
theorem helper : True := trivial

/-- The advertised theorem. -/
theorem main (p : Prop) (hp : p) :
    p ∧ True :=
  ⟨hp, helper⟩
end Helpers

end TruthCore.Results.Bar
"""


class ChallengeTextTest(unittest.TestCase):
    def test_keeps_named_signatures_with_sorry_and_drops_helpers(self) -> None:
        text = argument_batch.challenge_text(SOLUTION, ["main"])
        self.assertIn("import TruthCore.Foo", text)
        self.assertNotIn("public import", text)
        self.assertNotIn("module", text.splitlines()[0])
        self.assertIn("theorem main (p : Prop) (hp : p) :\n    p ∧ True := by\n  sorry", text)
        self.assertNotIn("helper", text)
        self.assertIn("open TruthCore.Foo", text)
        self.assertIn("end TruthCore.Results.Bar", text)
        self.assertIn("namespace Control", text)
        self.assertIn("end Control", text)
        self.assertNotIn("end Helpers", text)
        self.assertIn("end of things, section headings and theorem names. -/", text)

    def test_missing_theorem_is_an_error(self) -> None:
        with self.assertRaises(SystemExit):
            argument_batch.challenge_text(SOLUTION, ["absent"])


class HandlesTest(unittest.TestCase):
    """Spec handles resolve to uuids; new records get uuid4 ids and plain labels."""

    def test_legacy_handle_resolves_and_new_records_need_a_plain_label(self) -> None:
        from corpus_ids import is_uuid, legacy_uuid

        handles = argument_batch.Handles()
        self.assertEqual(handles.get("statement", "STMT-EXCLUDED-MIDDLE"),
                         legacy_uuid("statement", "STMT-EXCLUDED-MIDDLE"))
        minted = handles.get("statement", "brand new handle", "A brand new proposition for the test")
        self.assertTrue(is_uuid(minted))
        self.assertNotEqual(minted, legacy_uuid("statement", "brand new handle"))
        self.assertEqual(handles.ref("statement", "brand new handle"), minted)
        with self.assertRaises(SystemExit):
            handles.get("statement", "STMT-NOT-A-RECORD-YET")


class SenseForkGenerationTest(unittest.TestCase):
    def test_uuid_fork_records_are_stable_across_regeneration(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            corpus = root / "corpus"
            statement_id = str(uuid.uuid4())
            senses = [str(uuid.uuid4()), str(uuid.uuid4())]
            for kind, records in {
                "statements": [{"id": statement_id, "label": "A test proposition", "paraphrase": "A"}],
                "definitions": [{"id": "e0b74ad0-25a4-4ce0-b739-7a99ba4c771c", "label": "Test sense", "term": "test"}],
                "disambiguations": [{"id": str(uuid.uuid4()), "term_label": "PRIOR", "senses": [
                    {"id": sid, "label": f"PRIOR_{n}"} for n, sid in enumerate(senses, 1)]}],
            }.items():
                (corpus / kind).mkdir(parents=True)
                for record in records:
                    (corpus / kind / f"{record['id']}.json").write_text(json.dumps(record))
            spec = {
                "batch": {"vocab": "TruthCore.Test", "results": "TruthCore.Results.Test"},
                "argument": [{"label": "Priority consequence", "rule": "identity", "meaning": "A implies A",
                    "research_comparisons": [{"target_statement_id": "A test proposition", "rival_statement_id": "A test proposition", "sense_definition_id": "Test sense", "outcome": "untested", "conditions": "test", "scope": "test", "coverage": "unknown", "exclusivity": "unknown", "next_step": "test"}],
                    "for_each_sense": {"term": "PRIOR", "senses": ["PRIOR_1", "PRIOR_2"]},
                    "cases": {f"PRIOR_{n}": {"theorem": f"case{n}", "premises": [statement_id],
                                               "conclusion": statement_id} for n in (1, 2)}}],
            }
            with patch.object(argument_batch, "ROOT", root), patch.object(argument_batch, "CORPUS", corpus):
                self.assertTrue(argument_batch.build_records(spec, True))
                records = [json.loads(p.read_text()) for p in (corpus / "arguments").glob("*.json")]
                self.assertEqual({r["term_senses"]["PRIOR"] for r in records}, set(senses))
                self.assertEqual(len({r["id"] for r in records}), 2)
                result = json.loads(next((corpus / "results").glob("*.json")).read_text())
                self.assertEqual(result["research_comparisons"][0]["target_statement_id"], statement_id)
                self.assertEqual(result["research_comparisons"][0]["sense_definition_id"], "e0b74ad0-25a4-4ce0-b739-7a99ba4c771c")
                self.assertEqual(argument_batch.build_records(spec, False), [])


class CommandSmokeTests(unittest.TestCase):
    def test_empty_map(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "map.toml"
            path.write_text('target = "test"\n')
            self.assertEqual(argument_batch.check_map(path, False), 0)

    def test_materialized_map_mode_preserves_default_and_rejects_missing_text(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "map.toml"
            path.write_text('[[node]]\nid="STMT-EXCLUDED-MIDDLE"\nnew=true\ntext="Designed node"\n')
            self.assertEqual(argument_batch.check_map(path, False), 1)
            self.assertEqual(argument_batch.check_map(path, False, allow_materialized_nodes=True), 0)
            path.write_text('[[node]]\nid="STMT-EXCLUDED-MIDDLE"\nnew=true\n')
            self.assertEqual(argument_batch.check_map(path, False, allow_materialized_nodes=True), 1)

    def test_materialized_map_edges_match_only_declared_statement_identities(self):
        from corpus_ids import legacy_uuid
        statement = legacy_uuid("statement", "STMT-EXCLUDED-MIDDLE")
        other = legacy_uuid("statement", "STMT-CATHOLICISM-TRUE")
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "map.toml"
            text = ('[[node]]\nid="STMT-EXCLUDED-MIDDLE"\n[[edge]]\n'
                    f'premises=["{statement}"]\nconclusion="STMT-EXCLUDED-MIDDLE"\n')
            path.write_text(text)
            self.assertEqual(argument_batch.check_map(path, False), 1)
            self.assertEqual(argument_batch.check_map(path, False, allow_materialized_nodes=True), 0)
            path.write_text(text.replace(statement, other))
            self.assertEqual(argument_batch.check_map(path, False, allow_materialized_nodes=True), 1)

    def test_fix_without_arguments(self):
        from subprocess import CompletedProcess
        with patch.object(argument_batch.subprocess, "run", return_value=CompletedProcess([], 0, "", "")):
            self.assertEqual(argument_batch.fix_disambiguations({}), 0)


if __name__ == "__main__":
    unittest.main()
