"""The #207 logical microcase, without confusing verified arrows and grounding."""
import json
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import corpus
from corpus_ids import Aliases, legacy_uuid  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
FIXTURE = json.loads((ROOT / "scripts/testdata/objective-truth-pilot.json").read_text())


ALIASES = Aliases.load(corpus.ROOT)


def selected(kind, ids):
    """Records of `kind` named by uuid, or by the legacy id behind a uuid of
    another kind (a migrated result and its argument share their legacy id)."""
    legacy = {ALIASES.legacy(record_id) for record_id in ids}
    return [record for _, record in corpus.load_dir(kind)
            if record["id"] in ids or record.get("legacy_id") in legacy]


class ObjectiveTruthPilotTest(unittest.TestCase):
    def test_actual_reciprocal_results_need_independent_grounding(self):
        statements = selected("statements", FIXTURE["statement_ids"])
        arguments = selected("arguments", FIXTURE["argument_ids"])
        for case in FIXTURE["cases"]:
            with self.subTest(case=case["id"]):
                results = selected("results", case["result_ids"])
                report = corpus.frontier_report(statements, arguments, results, [])
                self.assertEqual(sorted(report["established_statements"]), sorted(case["expected_established"]))
                self.assertEqual(len(statements), 2)  # no equivalence-induced identity merge

    def test_semantic_bridge_stays_open_despite_a_verified_conditional(self):
        arguments = selected("arguments", [legacy_uuid("argument", "PILOT-STABLE-SENTENCE-EXCLUDES-GLOBAL-VARIATION")])
        ids = [legacy_uuid("statement", "STMT-PILOT-LOGICAL-SENTENCE-STABLE"), legacy_uuid("statement", "STMT-PILOT-NOT-GLOBAL-PROFILE-VARIATION")]
        report = corpus.frontier_report(selected("statements", ids), arguments,
                                       selected("results", [arguments[0]["id"]]), [])
        self.assertIn(ids[0], [item["statement_id"] for item in report["items"]])
        self.assertNotIn(ids[1], report["established_statements"])

    def test_logical_theorems_do_not_refute_withholding_or_all_relative_readings(self):
        pilot_arguments = set(FIXTURE["argument_ids"]) | {legacy_uuid("argument", "PILOT-CONFLICTING-OPINIONS-TEST")}
        for _, relation in corpus.load_dir("relations"):
            if relation["subject_id"] in pilot_arguments:
                self.assertNotEqual(relation["predicate"], "refutes")
        for sid in [legacy_uuid("statement", "STMT-EXCLUDED-MIDDLE-WITHHELD-INTUITIONISM"),
                    legacy_uuid("statement", "STMT-PILOT-GLOBAL-PROFILE-VARIATION"), legacy_uuid("statement", "STMT-PILOT-LOCAL-PROFILE-VARIATION")]:
            self.assertEqual(len(selected("statements", [sid])), 1)


if __name__ == "__main__":
    unittest.main()
