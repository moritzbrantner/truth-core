"""Schema registrations require proof obligations, not resemblance or source support."""

from __future__ import annotations

import argparse
import contextlib
import copy
import io
import unittest
from pathlib import Path
from unittest.mock import patch

import corpus


class SchemaRegistrationTest(unittest.TestCase):
    def setUp(self):
        self.path = corpus.ROOT / "corpus/relations/test.json"
        self.relation = {
            "id": "REL-INSTANCE",
            "predicate": "instance_of_schema",
            "subject_kind": "statement",
            "subject_id": "INSTANCE",
            "object_kind": "statement",
            "object_id": "SCHEMA",
            "verification_result_id": "PACKAGE",
            "instance_theorem": "TruthCore.Results.Test.instanceProof",
            "schema_theorem": "TruthCore.Results.Test.schemaProof",
            "note": "Conditional instance, not source support or frontier closure.",
        }
        self.results = {"PACKAGE": {"solution_module": "TruthCore.Results.Test.Solution"}}
        self.configs = {"PACKAGE": {"theorem_names": [
            self.relation["instance_theorem"], self.relation["schema_theorem"],
        ]}}

    def validate(self, relation):
        corpus.validate_premise_program_relation(self.path, relation)
        corpus.validate_schema_registration(self.path, relation, self.results, self.configs)

    def test_requires_two_statement_endpoints(self):
        self.validate(self.relation)
        for field in ("subject_kind", "object_kind"):
            with self.subTest(field=field), self.assertRaises(corpus.CorpusError):
                self.validate({**self.relation, field: "claim"})

    def test_rejects_missing_unknown_or_unlisted_proof_evidence(self):
        for field in ("verification_result_id", "instance_theorem", "schema_theorem", "note"):
            altered = {key: value for key, value in self.relation.items() if key != field}
            with self.subTest(missing=field), self.assertRaises(corpus.CorpusError):
                self.validate(altered)
        for note in (" ", 1):
            with self.subTest(note=note), self.assertRaises(corpus.CorpusError):
                self.validate({**self.relation, "note": note})
        for field in ("verification_result_id", "instance_theorem", "schema_theorem"):
            with self.subTest(unknown=field), self.assertRaises(corpus.CorpusError):
                self.validate({**self.relation, field: "UNKNOWN"})

    def test_binds_each_named_proof_to_its_statement_and_rejects_extra_assumptions(self):
        bindings = corpus.schema_binding_records([self.relation], self.results)
        self.assertEqual([a["conclusion_statement_id"] for _, a in bindings], ["INSTANCE", "SCHEMA"])
        index = {
            name: (Path(name), {"lean_declaration": f"TruthCore.Test.{name}"})
            for name in ("INSTANCE", "SCHEMA")
        }
        for binding, argument in bindings:
            goal = argument["conclusion_statement_id"]
            described = {"binders": [], "result": {
                "head": f"TruthCore.Test.{goal}", "type": goal, "prop": True,
            }}
            self.assertEqual(corpus.bind_result(binding, argument, index, described)["status"], "bound")
            wrong = copy.deepcopy(described)
            wrong["result"]["head"] = "TruthCore.Test.Unrelated"
            self.assertEqual(corpus.bind_result(binding, argument, index, wrong)["status"], "mismatch")
            conditional = copy.deepcopy(described)
            conditional["binders"] = [{
                "name": "unproved", "head": "TruthCore.Test.Assumption", "prop": True,
                "type": "TruthCore.Test.Assumption",
            }]
            self.assertEqual(corpus.bind_result(binding, argument, index, conditional)["status"], "mismatch")

    def test_registration_neither_sources_nor_closes_statements(self):
        statements = [{"id": name, "paraphrase": name} for name in ("INSTANCE", "SCHEMA")]
        baseline = corpus.frontier_report(statements, [], [], [], root="SCHEMA")
        registered = corpus.frontier_report(statements, [], [], [self.relation], root="SCHEMA")
        self.assertEqual(registered, baseline)
        self.assertEqual(registered["established_statements"], [])


    def test_bind_command_composes_schema_bindings_and_live_model_gate(self):
        result = {"id": "PACKAGE", **self.results["PACKAGE"], "theorem": "packageProof"}
        records = {
            "results": [(self.path, result)],
            "relations": [(self.path, self.relation)],
            "statements": [(self.path, {"id": name}) for name in ("INSTANCE", "SCHEMA")],
        }
        read_text = Path.read_text

        def fixture_text(path, *args, **kwargs):
            # Only stub the saved Lean response. Contract registrations and
            # other independent repository inputs must retain their contents.
            return "[]" if path == Path("fixture.json") else read_text(path, *args, **kwargs)

        for fixture_only in (False, True):
            with self.subTest(fixture_only=fixture_only):
                report = {"summary": {"bound": 0, "pinned": 0, "mismatch": 0}, "stale_pins": []}
                args = argparse.Namespace(lean_json="fixture.json" if fixture_only else None, json=True)
                with (
                    patch.object(corpus, "validate"),
                    patch.object(corpus, "load_dir", side_effect=lambda name: records[name]),
                    patch.object(corpus, "run_bind_tool", return_value=[]) as describe,
                    patch.object(corpus, "bind_report", return_value=report) as bind,
                    patch.object(corpus, "registered_models", return_value=[{"id": "MODEL-TEST"}]),
                    patch.object(corpus, "verify_models", return_value={"models": 1}) as models,
                    patch.object(Path, "read_text", autospec=True, side_effect=fixture_text),
                    contextlib.redirect_stdout(io.StringIO()),
                ):
                    self.assertEqual(corpus.command_bind_check(args), 0)
                    bindings = bind.call_args.args[1]
                    self.assertEqual(len(bindings), 2)
                    if fixture_only:
                        describe.assert_not_called()
                        models.assert_not_called()
                    else:
                        self.assertEqual(set(describe.call_args.args[0]["theorems"]), {
                            "packageProof", self.relation["instance_theorem"], self.relation["schema_theorem"],
                        })
                        models.assert_called_once_with(
                            [{"id": "MODEL-TEST"}],
                            {name: {"id": name} for name in ("INSTANCE", "SCHEMA")}, corpus.ROOT,
                        )
                        models.side_effect = ValueError("model certificate rejected")
                        with self.assertRaisesRegex(corpus.CorpusError, "model certificate rejected"):
                            corpus.command_bind_check(args)


if __name__ == "__main__":
    unittest.main()
