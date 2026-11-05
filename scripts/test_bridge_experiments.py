"""Cheap, local regression guards for the research-bridge discovery view."""
from __future__ import annotations

import tempfile
from pathlib import Path
import unittest

from bridge_experiments import experiment_report, format_experiments


class BridgeExperimentsTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.profile = "TruthCore.Semantics.Shared"
        self.anchor = "RESULT-A"
        self.source = "TruthCore.Results.Source.Solution"
        self.consumer = "TruthCore.Results.Consumer.Solution"
        self.module(self.profile, "namespace TruthCore.Semantics.Shared\nend TruthCore.Semantics.Shared\n")
        self.module(self.source, f"import {self.profile}\n")
        self.module(self.consumer, f"import {self.source}\n")
        self.arguments = [
            {"id": "ARG-A", "premise_statement_ids": ["STMT-A", "STMT-B"],
             "conclusion_statement_id": "STMT-C"},
            {"id": "ARG-B", "premise_statement_ids": ["STMT-C", "STMT-E"],
             "conclusion_statement_id": "STMT-D"},
        ]
        self.results = [
            {"id": self.anchor, "argument_id": "ARG-A", "solution_module": self.source,
             "theorem": "Test.source", "status": "solution-present"},
            {"id": "RESULT-B", "argument_id": "ARG-B", "solution_module": self.consumer,
             "theorem": "Test.consumer", "status": "solution-present"},
        ]
        self.attempts = [{"id": "ATTEMPT-X", "outcome": "succeeded",
                          "statement_ids": ["STMT-C", "STMT-D"],
                          "evidence": [self.anchor, "RESULT-B"],
                          "blocker": "One independently defended bridge is missing."}]
        self.frontier = {"reaching_root_statements": ["STMT-C"], "closed_statements": {}}

    def module(self, name, source):
        path = self.root / (name.replace(".", "/") + ".lean")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(source, encoding="utf-8")

    def report(self, limit=5):
        statements = [{"id": sid} for sid in ("STMT-A", "STMT-B", "STMT-C", "STMT-D", "STMT-E")]
        return experiment_report(self.root, {"statements": statements, "arguments": self.arguments,
                                             "results": self.results, "attempts": self.attempts},
                                 self.frontier, self.anchor, self.profile, limit=limit)

    def test_direct_import_keeps_whole_and_bundle(self):
        item = self.report()["experiments"][0]
        bundles = {entry["result_id"]: entry for entry in item["full_argument_bundles"]}
        self.assertEqual(bundles["RESULT-A"]["premise_statement_ids"], ["STMT-A", "STMT-B"])
        self.assertEqual(bundles["RESULT-B"]["premise_statement_ids"], ["STMT-C", "STMT-E"])
        self.assertEqual(item["exact_import_edges"], [
            {"consumer_result_id": "RESULT-B", "imported_result_id": "RESULT-A"}])
        self.assertIn("No", format_experiments({**self.report(), "experiments": []}))
        self.assertNotIn("entailed", item["qualification"])

    def test_attempt_evidence_without_explicit_focus_is_not_automatically_joined(self):
        # This is how a broad survey can cite a theorem from a different profile.
        self.attempts[0]["statement_ids"] = ["STMT-D"]
        output = self.report()
        self.assertFalse(output["experiments"])
        self.assertGreater(output["summary"]["excluded_peer_reasons"]["cross_profile"], 0)
        self.assertIn("NOT a refutation", output["absence_warning"])

    def test_explicit_witness_mismatch_excludes_direct_import(self):
        self.results[0]["witness_id"] = "PINNED-EDITION-A"
        self.results[1]["witness_id"] = "PINNED-EDITION-B"
        output = self.report()
        self.assertEqual(output["experiments"], [])
        self.assertEqual(output["summary"]["excluded_peer_reasons"]["different_witness"], 1)

    def test_unrelated_semantic_module_rejected_even_if_attempt_co_mentions(self):
        self.module(self.consumer, "import TruthCore.Unrelated\n")
        self.module("TruthCore.Unrelated", "namespace TruthCore.Unrelated\nend TruthCore.Unrelated\n")
        output = self.report()
        self.assertEqual(output["experiments"], [])
        self.assertEqual(output["summary"]["excluded_peer_reasons"]["cross_profile"], 1)

    def test_same_imported_profile_without_proof_reuse_is_not_a_bridge(self):
        self.module(self.consumer, f"import {self.profile}\n")
        output = self.report()
        self.assertEqual(output["experiments"], [])
        self.assertEqual(output["summary"]["excluded_peer_reasons"]["no_direct_reuse"], 1)

    def test_missing_proof_is_not_a_falsification(self):
        self.attempts[0]["evidence"] = [self.anchor]
        output = self.report()
        self.assertEqual(output["summary"]["eligible_experiments"], 0)
        self.assertIn("NOT a refutation", output["absence_warning"])

    def test_negative_controls_receive_priority_only_within_profile(self):
        self.attempts.append({"id": "ATTEMPT-Y", "outcome": "succeeded",
                              "statement_ids": ["STMT-C", "STMT-D"],
                              "evidence": [self.anchor, "RESULT-B", "OMISSION-CONTROL"],
                              "blocker": "A second unresolved test."})
        self.results.append({"id": "OMISSION-CONTROL", "argument_id": "ARG-A",
                             "solution_module": self.source})
        output = self.report(limit=1)
        self.assertEqual(output["experiments"][0]["attempt_id"], "ATTEMPT-Y")
        self.assertEqual(output["truncated"], 1)
        self.results[-1]["semantic_profile_id"] = "different"
        output = self.report(limit=2)
        self.assertEqual([item["attempt_id"] for item in output["experiments"]], ["ATTEMPT-X", "ATTEMPT-Y"])
        self.assertEqual(output["experiments"][1]["control_hint_result_ids"], [])

    def test_invalid_profile_and_limit_fail_closed(self):
        with self.assertRaisesRegex(ValueError, "profile module"):
            experiment_report(self.root, {"results": self.results, "arguments": self.arguments,
                                          "statements": [], "attempts": []}, {}, self.anchor, "../../unsafe")
        with self.assertRaisesRegex(ValueError, "limit"):
            self.report(limit=0)


if __name__ == "__main__":
    unittest.main()
