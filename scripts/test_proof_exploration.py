"""Composition fixture uses the real pilot records and authoritative frontier."""
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import corpus


def selected(kind, ids):
    return [record for _, record in corpus.load_dir(kind) if record["id"] in ids]


class ProofExplorationTest(unittest.TestCase):
    def test_grounded_intermediate_composition_closes_conjunction(self):
        target = "STMT-PILOT-WITNESS-AND-CONSEQUENCE"
        result_id = "PILOT-COMPOSED-WITNESS"
        arguments = selected("arguments", [result_id])
        self.assertEqual(arguments[0]["premise_statement_ids"], [])
        self.assertEqual(arguments[0]["inference_ids"], [
            "INF-LOGIC-SOME-PROPOSITION-HOLDS",
            "INF-LOGIC-SOME-HOLDS-ENTAILS-NOT-ALL-FAIL",
            "INF-LOGIC-NOT-ALL-FAIL-ENTAILS-SOME-HOLDS",
            "INF-PILOT-WITNESS-AND-CONSEQUENCE",
        ])
        statements = selected("statements", [target])
        report = corpus.frontier_report(statements, arguments,
                                       selected("results", [result_id]), [], root=target)
        self.assertIn(target, report["established_statements"])
        self.assertEqual(report["items"], [])

    def test_actual_a_to_b_to_c_results_require_independent_a(self):
        a = "STMT-SOME-LEAN-PROPOSITION-HOLDS"
        b = "STMT-NOT-EVERY-LEAN-PROPOSITION-FAILS"
        c = "STMT-PILOT-WITNESS-AND-CONSEQUENCE"
        chain = ["LOGIC-SOME-HOLDS-ENTAILS-NOT-ALL-FAIL",
                 "PILOT-CONSEQUENCE-ENTAILS-CONJUNCTION"]
        statements = selected("statements", [a, b, c])
        arguments = selected("arguments", chain + ["LOGIC-SOME-PROPOSITION-HOLDS"])
        ungrounded = corpus.frontier_report(statements, arguments,
                                            selected("results", chain), [], root=c)
        self.assertNotIn(c, ungrounded["established_statements"])
        grounded = corpus.frontier_report(statements, arguments,
                                          selected("results", chain + ["LOGIC-SOME-PROPOSITION-HOLDS"]), [], root=c)
        self.assertEqual(grounded["established_statements"], sorted([a, b, c]))
        helper = selected("arguments", [chain[1]])[0]
        self.assertEqual(helper["premise_statement_ids"], [b])
        self.assertEqual(helper["conclusion_statement_id"], c)

    def test_profile_stability_is_still_an_open_interpretation_obligation(self):
        ids = ["STMT-PILOT-LOGICAL-SENTENCE-STABLE", "STMT-PILOT-NOT-GLOBAL-PROFILE-VARIATION"]
        result_id = "PILOT-STABLE-SENTENCE-EXCLUDES-GLOBAL-VARIATION"
        report = corpus.frontier_report(selected("statements", ids),
                                       selected("arguments", [result_id]),
                                       selected("results", [result_id]), [], root=ids[1])
        self.assertNotIn(ids[1], report["established_statements"])
        self.assertIn(ids[0], [item["statement_id"] for item in report["items"]])


if __name__ == "__main__":
    unittest.main()
