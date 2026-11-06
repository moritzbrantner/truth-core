#!/usr/bin/env python3
"""Actual-record closure counterfactuals; synthetic refutations are NOT research claims."""
import copy
import json
import sys
import unittest
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
import corpus
ROOT = Path(__file__).resolve().parent.parent


def record(kind, key):
    for path in (ROOT / "corpus" / kind).glob("*.json"):
        item = json.loads(path.read_text())
        if item["id"] == key:
            return item
    raise AssertionError(key)


class SemanticRivalScopeTest(unittest.TestCase):
    def check_counterfactual(self, rival, target, relation_id=None):
        statements = [record("statements", key) for key in (rival, target)]
        # Isolate rival authority; no corpus floor is edited.
        for item in statements:
            item.pop("self_evident", None)
        statements.append({"id": "TEST-NOT-RAW", "paraphrase": "Hypothetical only"})
        argument = {"id": "TEST-REFUTATION", "premise_statement_ids": [],
                    "conclusion_statement_id": "TEST-NOT-RAW", "inference_ids": []}
        refutation = {"id": "TEST-REFUTES", "subject_kind": "argument",
                      "subject_id": "TEST-REFUTATION", "predicate": "refutes",
                      "object_kind": "statement", "object_id": rival}
        actual = [record("relations", relation_id)] if relation_id else []
        def report(relations):
            return corpus.frontier_report(copy.deepcopy(statements), [argument],
                [{"id": "TEST-RESULT", "argument_id": argument["id"]}],
                [refutation, *relations], root=target)
        fixed = report(actual)
        self.assertIn(rival, fixed["refuted_statements"])
        self.assertNotIn(target, fixed["closed_statements"])
        self.assertNotIn(target, fixed["established_statements"])
        # Reconstruct only the unsafe legacy rival edge; same records/refutation.
        legacy = {"id": "TEST-LEGACY", "subject_kind": "statement",
                  "subject_id": rival, "predicate": "alternative_to",
                  "object_kind": "statement", "object_id": target}
        self.assertEqual(report([legacy])["closed_statements"][target], "alternatives_refuted")

    def test_truth_accounts_are_not_logical_rivals(self):
        self.assertFalse((ROOT / "corpus/relations/rel-truth-is-provability-alternative-to-thought-true-by-composition.json").exists())
        self.check_counterfactual("STMT-TRUTH-IS-PROVABILITY-INTUITIONISM",
                                  "STMT-THOUGHT-TRUE-OR-FALSE-BY-COMPOSITION")

    def test_tlp_objection_is_not_exhaustive_negative_arguability(self):
        self.check_counterfactual("STMT-TLP-GOD-SENTENCES-NONSENSICAL",
            "STMT-NATURAL-THEOLOGY-ARGUABLE",
            "REL-TLP-GOD-SENTENCES-ALTERNATIVE-TO-NATURAL-THEOLOGY-ARGUABLE")

    def test_pla_readings_are_interpretive_objections(self):
        self.check_counterfactual("STMT-PLA-NONSENSE-READING", "STMT-PLA-REDUCTIO-READING",
            "REL-PLA-NONSENSE-ALTERNATIVE-TO-REDUCTIO-READING")

    def test_explanation_rival_is_exact_guarded_negative(self):
        relation = record("relations", "REL-ANTIREALIST-ORDER-ALTERNATIVE-TO-REALIST-ORDER-OF-EXPLANATION")
        self.assertEqual(relation["subject_id"], "STMT-NOT-REALIST-EXPLANATORY-ORDER")
        argument = record("arguments", "ANTIREALIST-ORDER-GUARDED-NOT-REALIST")
        self.assertEqual(set(argument["premise_statement_ids"]), {
            "STMT-ANTIREALIST-ORDER-OF-EXPLANATION", "STMT-EXPLANATORY-ORDER-ASYMMETRIC",
            "STMT-GEACH-MINOR-PREMISE-IS-MORAL"})


if __name__ == "__main__":
    unittest.main()
