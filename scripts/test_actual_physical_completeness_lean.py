"""Elaborate full-domain coverage, knowledge-transfer and failure controls."""
from pathlib import Path
import subprocess
import unittest

from lean_test_support import requires_built

ROOT = Path(__file__).resolve().parents[1]


@requires_built('TruthCore.Logic.ActualPhysicalCompleteness',
                'TruthCore.Logic.KnowledgeAdmissibility')
class ActualPhysicalCompletenessTest(unittest.TestCase):
    def test_full_domain_controls(self):
        result = subprocess.run(
            ['python3', 'scripts/worker_env.py', '--', 'lake', 'env', 'lean',
             'scripts/fixtures/ActualPhysicalCompleteness.lean'],
            cwd=ROOT, capture_output=True, text=True,
        )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertNotIn('sorry', result.stdout + result.stderr)
