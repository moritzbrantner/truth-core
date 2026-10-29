import copy
import json
from pathlib import Path
import subprocess
import unittest

import bundle_audit


class BundleAuditTest(unittest.TestCase):
    def test_exact_live_record_coverage(self):
        audit = bundle_audit.check()
        self.assertEqual(len(audit['records']), 69)
        self.assertEqual(sum(row['kind'] == 'statements' for row in audit['records']), 21)

    def test_all_specialization_and_consumer_scope(self):
        audit = bundle_audit.check(audit=json.loads(bundle_audit.AUDITS[1].read_text()))
        self.assertEqual(len(audit['records']), 149)
        self.assertEqual(sum(row['kind'] == 'results' for row in audit['records']), 5)
        missing = copy.deepcopy(audit)
        missing['consumer_result_ids'].pop()
        with self.assertRaisesRegex(ValueError, 'coverage'):
            bundle_audit.check(audit=missing)

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

    @unittest.skipUnless((Path.home() / '.elan/bin/lake').exists(), 'requires pinned Lean')
    def test_preservation_and_vacuity_controls(self):
        run = subprocess.run(['python3', 'scripts/worker_env.py', '--', 'lake', 'env', 'lean',
                              'scripts/fixtures/ClassicalAttributesMigration.lean'],
                             cwd=bundle_audit.ROOT, text=True, capture_output=True)
        self.assertEqual(run.returncode, 0, run.stdout + run.stderr)
        self.assertNotIn('sorry', run.stdout + run.stderr)

    def test_specialized_inhabited_and_split_witness_controls(self):
        run = subprocess.run(['python3', 'scripts/worker_env.py', '--', 'lake', 'env', 'lean',
                              'scripts/fixtures/ClassicalAttributesAllMigration.lean'],
                             cwd=bundle_audit.ROOT, text=True, capture_output=True)
        self.assertEqual(run.returncode, 0, run.stdout + run.stderr)
        self.assertNotIn('sorry', run.stdout + run.stderr)


if __name__ == '__main__':
    unittest.main()
