"""Composition fixture uses the real pilot records and authoritative frontier."""
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import corpus
from corpus_ids import Aliases, legacy_uuid  # noqa: E402


ALIASES = Aliases.load(corpus.ROOT)


def selected(kind, ids):
    """Records of `kind` named by uuid, or by the legacy id behind a uuid of
    another kind (a migrated result and its argument share their legacy id)."""
    legacy = {ALIASES.legacy(record_id) for record_id in ids}
    return [record for _, record in corpus.load_dir(kind)
            if record["id"] in ids or record.get("legacy_id") in legacy]


class ProofExplorationTest(unittest.TestCase):
    def test_grounded_intermediate_composition_closes_conjunction(self):
        target = legacy_uuid("statement", "STMT-PILOT-WITNESS-AND-CONSEQUENCE")
        result_id = legacy_uuid("result", "PILOT-COMPOSED-WITNESS")
        arguments = selected("arguments", [result_id])
        self.assertEqual(arguments[0]["premise_statement_ids"], [])
        self.assertEqual(arguments[0]["inference_ids"], [
            legacy_uuid("inference", "INF-LOGIC-SOME-PROPOSITION-HOLDS"),
            legacy_uuid("inference", "INF-LOGIC-SOME-HOLDS-ENTAILS-NOT-ALL-FAIL"),
            legacy_uuid("inference", "INF-LOGIC-NOT-ALL-FAIL-ENTAILS-SOME-HOLDS"),
            legacy_uuid("inference", "INF-PILOT-WITNESS-AND-CONSEQUENCE"),
        ])
        statements = selected("statements", [target])
        report = corpus.frontier_report(statements, arguments,
                                       selected("results", [result_id]), [], root=target)
        self.assertIn(target, report["established_statements"])
        self.assertEqual(report["items"], [])

    def test_actual_a_to_b_to_c_results_require_independent_a(self):
        a = legacy_uuid("statement", "STMT-SOME-LEAN-PROPOSITION-HOLDS")
        b = legacy_uuid("statement", "STMT-NOT-EVERY-LEAN-PROPOSITION-FAILS")
        c = legacy_uuid("statement", "STMT-PILOT-WITNESS-AND-CONSEQUENCE")
        chain = [legacy_uuid("result", "LOGIC-SOME-HOLDS-ENTAILS-NOT-ALL-FAIL"),
                 legacy_uuid("result", "PILOT-CONSEQUENCE-ENTAILS-CONJUNCTION")]
        statements = selected("statements", [a, b, c])
        arguments = selected("arguments", chain + [legacy_uuid("argument", "LOGIC-SOME-PROPOSITION-HOLDS")])
        ungrounded = corpus.frontier_report(statements, arguments,
                                            selected("results", chain), [], root=c)
        self.assertNotIn(c, ungrounded["established_statements"])
        grounded = corpus.frontier_report(statements, arguments,
                                          selected("results", chain + [legacy_uuid("result", "LOGIC-SOME-PROPOSITION-HOLDS")]), [], root=c)
        self.assertEqual(sorted(grounded["established_statements"]), sorted([a, b, c]))
        helper = selected("arguments", [chain[1]])[0]
        self.assertEqual(helper["premise_statement_ids"], [b])
        self.assertEqual(helper["conclusion_statement_id"], c)

    def test_profile_stability_is_still_an_open_interpretation_obligation(self):
        ids = [legacy_uuid("statement", "STMT-PILOT-LOGICAL-SENTENCE-STABLE"), legacy_uuid("statement", "STMT-PILOT-NOT-GLOBAL-PROFILE-VARIATION")]
        result_id = legacy_uuid("result", "PILOT-STABLE-SENTENCE-EXCLUDES-GLOBAL-VARIATION")
        report = corpus.frontier_report(selected("statements", ids),
                                       selected("arguments", [result_id]),
                                       selected("results", [result_id]), [], root=ids[1])
        self.assertNotIn(ids[1], report["established_statements"])
        self.assertIn(ids[0], [item["statement_id"] for item in report["items"]])


if __name__ == "__main__":
    unittest.main()
