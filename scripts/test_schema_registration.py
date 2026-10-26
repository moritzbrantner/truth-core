"""Schema registrations require proof obligations, not resemblance or source support."""

from __future__ import annotations

import copy
import unittest
from pathlib import Path

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


if __name__ == "__main__":
    unittest.main()
