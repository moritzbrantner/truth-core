"""The work view uses frontier authority, including counterfactual closure cascades."""
import json
import unittest
from unittest.mock import patch

import corpus
from next_steps import validate_case_split, validate_settlement_actions


def statement(sid, **kwargs):
    return {"id": sid, "paraphrase": sid, **kwargs}


def argument(aid, premises, conclusion):
    return {"id": aid, "premise_statement_ids": premises,
            "conclusion_statement_id": conclusion, "inference_ids": ["INF-" + aid], "meaning": aid}


class NextStepsTest(unittest.TestCase):
    def report(self):
        # Settling A makes its refutation count, defeats rival R, defends B,
        # and thus removes two route leaves, not merely the A membership.
        statements = [statement(sid) for sid in ["ROOT", "A", "B", "R", "FALSE"]]
        arguments = [argument("ROOT-PROOF", ["A", "B"], "ROOT"),
                     argument("REFUTE-R", ["A"], "FALSE")]
        results = [{"id": "ROOT-RESULT", "argument_id": "ROOT-PROOF"},
                   {"id": "REFUTE-RESULT", "argument_id": "REFUTE-R"}]
        relations = [{"id": "RIVAL", "subject_kind": "statement", "subject_id": "R", "predicate": "alternative_to", "object_kind": "statement", "object_id": "B"},
                     {"id": "REFUTATION", "subject_kind": "argument", "subject_id": "REFUTE-R", "predicate": "refutes", "object_kind": "statement", "object_id": "R"}]
        return corpus.frontier_report(statements, arguments, results, relations, root="ROOT", _include_next_steps=True)

    def test_same_fixpoint_impact_includes_newly_counted_refutation(self):
        report = self.report()
        view = report["next_steps"]
        leaves = {leaf["statement_id"]: leaf for leaf in view["leaves"]}
        self.assertEqual(leaves["A"]["impact"]["routes"], [{"argument_id": "ROOT-PROOF", "before": 2, "after": 0, "drop": 2}])
        self.assertEqual(report["routes"]["routes"][0]["cost"], 2)
        self.assertNotIn("B", report["established_statements"])
        rival = leaves["B"]["rivals"][0]
        self.assertFalse(rival["refuted"])
        self.assertEqual(rival["refutations"][0]["unestablished_premise_statement_ids"], ["A"])

    def test_shared_failure_does_not_certify_joint_settlement(self):
        statements = [statement(sid) for sid in ["ROOT", "A", "B", "C"]]
        arguments = [argument("LEFT", ["A", "B"], "ROOT"), argument("RIGHT", ["A", "C"], "ROOT")]
        results = [{"id": aid, "argument_id": aid} for aid in ["LEFT", "RIGHT"]]
        view = corpus.frontier_report(statements, arguments, results, [], root="ROOT", _include_next_steps=True)["next_steps"]
        pair = view["joint_settlements"][0]
        self.assertEqual(pair["shared_statement_ids"], ["A"])
        self.assertFalse(pair["certified"])
        self.assertEqual(pair["left_failure_statement_ids"], ["A", "B"])
        self.assertIn("A", view["failure_modes"])
        self.assertEqual(view["failure_modes"]["A"]["recorded_rivals"], [])

    def test_empty_rivals_are_not_a_defense(self):
        leaves = self.report()["next_steps"]["leaves"]
        leaf = next(leaf for leaf in leaves if leaf["statement_id"] == "A")
        self.assertEqual(leaf["defense"]["recorded_rival_count"], 0)
        self.assertFalse(leaf["established"])
        self.assertTrue(leaf["floor"]["owner_decision_required"])

    def test_cli_is_a_projection_of_frontier_only(self):
        import argparse, contextlib, io
        report = self.report()
        output = io.StringIO()
        with patch.object(corpus, "current_frontier", return_value=report) as current:
            with contextlib.redirect_stdout(output):
                self.assertEqual(corpus.command_next_steps(argparse.Namespace(root="ROOT", json=True)), 0)
        current.assert_called_once_with("ROOT", False)
        self.assertEqual(json.loads(output.getvalue()), report["next_steps"])

    def test_partition_annotation_does_not_establish_target_or_defeat_cases(self):
        statements = [statement(sid) for sid in ["ROOT", "A", "B", "EM", "COVER"]]
        arguments = [argument("ROOT-PROOF", ["A"], "ROOT"), argument("COVERAGE", ["EM"], "COVER")]
        results = [{"id": "ROOT-RESULT", "argument_id": "ROOT-PROOF"},
                   {"id": "PARTITION", "argument_id": "COVERAGE", "theorem": "TruthCore.Test.coverage",
                    "case_split": {"target_statement_id": "A", "cases": [{"label": "other case", "lean_declaration": "TruthCore.Test.B", "statement_id": "B"}]}}]
        report = corpus.frontier_report(statements, arguments, results, [], root="ROOT", _include_next_steps=True)
        partition = report["next_steps"]["partitions"][0]
        self.assertFalse(partition["target_established"])
        self.assertFalse(partition["cases"][0]["refuted"])
        self.assertEqual(partition["missing_background_statement_ids"], ["EM"])
        self.assertNotIn("A", report["established_statements"])

    def test_conditional_route_leaf_keeps_its_source_depth(self):
        statements = [statement(sid) for sid in ["ROOT", "A", "X"]]
        arguments = [argument("ROOT-PROOF", ["A"], "ROOT"), argument("A-PROOF", ["X"], "A")]
        results = [{"id": aid, "argument_id": aid} for aid in ["ROOT-PROOF", "A-PROOF"]]
        report = corpus.frontier_report(statements, arguments, results, [], root="ROOT",
                                        claims=[{"id": "CLAIM-A", "statement_id": "A"}], _include_next_steps=True)
        leaf = report["next_steps"]["leaves"][0]
        self.assertEqual(leaf["statement_id"], "A")
        self.assertEqual(leaf["depth"], "stated")
        self.assertEqual(leaf["route_depths"]["ROOT-PROOF"], "proved_unestablished")
        self.assertFalse(leaf["established"])

    def test_next_projection_is_deterministic_under_input_reordering(self):
        statements = [statement(sid) for sid in ["ROOT", "A", "B"]]
        arguments = [argument("LEFT", ["A"], "ROOT"), argument("RIGHT", ["B"], "ROOT")]
        results = [{"id": aid, "argument_id": aid} for aid in ["LEFT", "RIGHT"]]
        expected = corpus.frontier_report(statements, arguments, results, [], root="ROOT", _include_next_steps=True)["next_steps"]
        actual = corpus.frontier_report(list(reversed(statements)), list(reversed(arguments)), list(reversed(results)), [], root="ROOT", _include_next_steps=True)["next_steps"]
        self.assertEqual(actual, expected)

    def test_case_split_requires_valid_exact_case_navigation(self):
        valid = {"case_split": {"target_statement_id": "A", "cases": [{"label": "case", "lean_declaration": "TruthCore.Example.cell"}], "survival_result_id": "SURVIVOR"}}
        validate_case_split(valid, {"A"}, {"SURVIVOR"})
        for invalid in ["MISSING", None]:
            with self.assertRaises(ValueError):
                validate_case_split({"case_split": {**valid["case_split"], "target_statement_id": invalid}}, {"A"}, {"SURVIVOR"})
        with self.assertRaises(ValueError):
            validate_case_split({"case_split": {**valid["case_split"], "cases": valid["case_split"]["cases"] * 2}}, {"A"}, {"SURVIVOR"})
        with self.assertRaises(ValueError):
            validate_case_split({"joint_settlement_schema": "true"}, set(), set())

    def test_navigation_approval_does_not_become_floor(self):
        valid = {"settlement_actions": [{"kind": "definition", "status": "approved", "description": "Adopt this reading", "decision": "https://github.com/moritzbrantner/truth-core/issues/1007#issuecomment-1"}]}
        validate_settlement_actions(valid)
        with self.assertRaises(ValueError):
            validate_settlement_actions({"settlement_actions": [{**valid["settlement_actions"][0], "decision": ""}]})
        record = statement("A", **valid)
        report = corpus.frontier_report([record, statement("ROOT")], [argument("ARG", ["A"], "ROOT")], [{"id": "RESULT", "argument_id": "ARG"}], [], root="ROOT", _include_next_steps=True)
        self.assertNotIn("A", report["established_statements"])
        self.assertEqual(report["next_steps"]["leaves"][0]["definition_decisions"], valid["settlement_actions"])

if __name__ == "__main__":
    unittest.main()
