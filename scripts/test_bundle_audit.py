import copy
import json
from pathlib import Path
import subprocess
import unittest

import bundle_audit
from lean_test_support import requires_built
from corpus_ids import legacy_uuid  # noqa: E402


class BundleAuditTest(unittest.TestCase):
    def test_exact_live_record_coverage(self):
        audit = bundle_audit.check()
        self.assertEqual(len(audit['records']), 70)
        self.assertIn(legacy_uuid('definition', 'DEF-EXCLUDED-MIDDLE-LOGICAL-HOLDING'),
                      {row['id'] for row in audit['records'] if row['kind'] == 'definitions'})
        self.assertEqual(sum(row['kind'] == 'statements' for row in audit['records']), 21)

    def test_all_specialization_and_consumer_scope(self):
        audit = bundle_audit.check(audit=json.loads(bundle_audit.AUDITS[1].read_text()))
        self.assertEqual(len(audit['records']), 152)
        self.assertTrue({legacy_uuid('definition', 'DEF-INDEPENDENT-POTENCY'), legacy_uuid('disambiguation', 'DISAMB-POTENCY')} <=
                        {row['id'] for row in audit['records']})
        self.assertEqual(sum(row['kind'] == 'results' for row in audit['records']), 5)
        missing = copy.deepcopy(audit)
        missing['consumer_result_ids'].pop()
        with self.assertRaisesRegex(ValueError, 'coverage'):
            bundle_audit.check(audit=missing)

    def test_naming_route_reuses_frozen_consumer_contract(self):
        audit = bundle_audit.check(audit=json.loads(bundle_audit.AUDITS[2].read_text()))
        index = bundle_audit.records(bundle_audit.ROOT)
        expected = bundle_audit.expected_scope(index, audit['result_id'])
        for result_id in audit['consumer_result_ids']:
            for kind, ids in bundle_audit.expected_scope(index, result_id).items():
                expected[kind].update(ids)
        self.assertEqual(
            {(row['kind'], row['id']) for row in audit['records']},
            {(kind, record_id) for kind, ids in expected.items() for record_id in ids},
        )
        semantic_rows = {
            legacy_uuid('statement', 'STMT-REVELATION-POSSIBLE-AND-RECOGNIZABLE'): {
                legacy_uuid('definition', 'DEF-REVELATION-RECOGNITION-PROFILE'),
                legacy_uuid('disambiguation', 'DISAMB-REVELATION-CAPABILITY-AND-PRACTICE-UPTAKE'),
            },
            legacy_uuid('statement', 'STMT-CHRIST-FOUNDED-VISIBLE-CHURCH'): {
                legacy_uuid('definition', 'DEF-CHURCH-CRITERION-CALIBRATION'),
            },
        }
        for statement_id, required in semantic_rows.items():
            statement = index['statements'][statement_id][1]
            links = set(statement.get('definition_ids', []) + statement.get('disambiguation_ids', []))
            if required & links:
                self.assertTrue(required <= links)
                self.assertTrue(required <= {row['id'] for row in audit['records']})
        self.assertTrue({legacy_uuid('definition', 'DEF-INDEPENDENT-POTENCY'), legacy_uuid('disambiguation', 'DISAMB-POTENCY')} <=
                        {row['id'] for row in audit['records']})
        self.assertEqual(sum(row['kind'] == 'results' for row in audit['records']), 11)
        self.assertEqual(len(audit['contract_baselines']), 11)
        missing = copy.deepcopy(audit)
        missing['contract_baselines'].pop(legacy_uuid('result', 'CATHOLICISM-STAGES-ONE-TWO-SAME-WITNESS'))
        with self.assertRaisesRegex(ValueError, 'scoped consumer'):
            bundle_audit.check(audit=missing)

    @requires_built('TruthCore.Results.Aquinas.SummaTheologiae.MaximeEnsIsGodViaFullDescriptionIdentity.Solution', 'TruthCore.Results.Aquinas.SummaTheologiae.FirstMoverIsMaximeEnsIdentity.Solution')
    @unittest.skipUnless((Path.home() / '.elan/bin/lake').exists(), 'requires pinned Lean')
    def test_conditional_bridges_do_not_supply_existence(self):
        run = subprocess.run(['python3', 'scripts/worker_env.py', '--', 'lake', 'env', 'lean',
                              'scripts/fixtures/NamingFirstMoverMigration.lean'],
                             cwd=bundle_audit.ROOT, text=True, capture_output=True)
        self.assertEqual(run.returncode, 0, run.stdout + run.stderr)
        self.assertNotIn('sorry', run.stdout + run.stderr)

    def test_missing_record_and_stale_review_are_rejected(self):
        audit = json.loads(bundle_audit.AUDIT.read_text())
        missing = copy.deepcopy(audit)
        missing['records'].pop()
        with self.assertRaisesRegex(ValueError, 'coverage'):
            bundle_audit.check(audit=missing)
        audit['records'][0]['reviewed_sha256'] = '0' * 64
        with self.assertRaisesRegex(ValueError, 'record change'):
            bundle_audit.check(audit=audit)

    def test_unresolved_record_needs_a_reason(self):
        audit = json.loads(bundle_audit.AUDIT.read_text())
        next(row for row in audit['records'] if row['status'] == 'unresolved')['finding'] = ''
        with self.assertRaisesRegex(ValueError, 'disposition'):
            bundle_audit.check(audit=audit)

    @requires_built('TruthCore.Results.Case.Catholicism.StageTwo.ClassicalAttributes.Solution')
    @unittest.skipUnless((Path.home() / '.elan/bin/lake').exists(), 'requires pinned Lean')
    def test_preservation_and_vacuity_controls(self):
        run = subprocess.run(['python3', 'scripts/worker_env.py', '--', 'lake', 'env', 'lean',
                              'scripts/fixtures/ClassicalAttributesMigration.lean'],
                             cwd=bundle_audit.ROOT, text=True, capture_output=True)
        self.assertEqual(run.returncode, 0, run.stdout + run.stderr)
        self.assertNotIn('sorry', run.stdout + run.stderr)

    @requires_built('TruthCore.Results.Case.Catholicism.StageTwo.ClassicalAttributesIdentity.Solution', 'TruthCore.Case.Catholicism.StagesOneTwo')
    @unittest.skipUnless((Path.home() / '.elan/bin/lake').exists(), 'requires pinned Lean')
    def test_specialized_inhabited_and_split_witness_controls(self):
        run = subprocess.run(['python3', 'scripts/worker_env.py', '--', 'lake', 'env', 'lean',
                              'scripts/fixtures/ClassicalAttributesAllMigration.lean'],
                             cwd=bundle_audit.ROOT, text=True, capture_output=True)
        self.assertEqual(run.returncode, 0, run.stdout + run.stderr)
        self.assertNotIn('sorry', run.stdout + run.stderr)


if __name__ == '__main__':
    unittest.main()
