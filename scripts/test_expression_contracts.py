"""Exact expression/dependency contracts against Lean, not a philosophical test."""
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import expression_contracts as contracts

ROOT = Path(__file__).resolve().parents[1]
NS = 'TruthCore.ContractFixture.'


@unittest.skipUnless(shutil.which('lake') or (Path.home() / '.elan/bin/lake').exists(), 'requires pinned Lean')
class ExpressionContractTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temp = tempfile.TemporaryDirectory()
        cls.directory = Path(cls.temp.name)
        source = (ROOT / 'scripts/fixtures/ExpressionContract.lean').read_text()
        cls.rows = cls.extract(source)
        cls.changed_law = cls.extract(source.replace('reflexive : ∀ a, relation a a',
            'reflexive : ∀ a b, relation a b → relation b a'))
        cls.changed_definition = cls.extract(source.replace('Prop := P ∧ Q', 'Prop := Q ∧ P')
            .replace('Prop := ∃ a, P a ∧ Q a', 'Prop := (∃ a, P a) ∧ (∃ a, Q a)'))

    @classmethod
    def extract(cls, source):
        directory = cls.directory
        path = directory / 'ExpressionContract.lean'
        path.write_text(source)
        run = ['python3', 'scripts/worker_env.py', '--', 'lake', 'env', 'lean']
        compiled = subprocess.run(run + [f'--root={directory}', '-o', str(directory / 'ExpressionContract.olean'), str(path)],
            cwd=ROOT, capture_output=True, text=True)
        if compiled.returncode:
            raise AssertionError(compiled.stdout + compiled.stderr)
        names = ['ordered', 'renamed', 'swapped', 'extraContext', 'instanceContext', 'lawContext', 'witnessContext']
        names = [NS + name for name in names]
        request = directory / 'request.json'
        request.write_text(json.dumps({'modules': ['ExpressionContract'], 'theorems': names, 'contract_theorems': names}))
        env = dict(os.environ, LEAN_PATH=str(directory) + os.pathsep + os.environ.get('LEAN_PATH', ''))
        completed = subprocess.run(run + ['--run', 'scripts/BindTypes.lean', str(request)], cwd=ROOT,
            env=env, capture_output=True, text=True)
        if completed.returncode:
            raise AssertionError(completed.stdout + completed.stderr)
        return {r['theorem'].removeprefix(NS): r for r in json.loads(completed.stdout)}

    @classmethod
    def tearDownClass(cls):
        cls.temp.cleanup()

    def summary(self, name, rows=None):
        return contracts.summarize((rows or self.rows)[name]['expression_contract'])

    def test_alpha_names_preserve_entire_contract(self):
        self.assertEqual(self.summary('ordered'), self.summary('renamed'))

    def test_argument_swaps_and_changed_contexts_are_rejected(self):
        old = self.summary('ordered')['type_sha256']
        for name in ['swapped', 'extraContext', 'instanceContext']:
            with self.subTest(name=name):
                self.assertNotEqual(old, self.summary(name)['type_sha256'])

    def test_law_received_through_structure_is_not_hidden(self):
        old, new = self.summary('lawContext'), self.summary('lawContext', self.changed_law)
        self.assertEqual(old['type_sha256'], new['type_sha256'])
        self.assertNotEqual(old['dependencies'][NS + 'Laws.mk'], new['dependencies'][NS + 'Laws.mk'])

    def test_definition_body_change_is_detected_beneath_unchanged_head(self):
        old, new = self.summary('ordered'), self.summary('ordered', self.changed_definition)
        self.assertEqual(old['type_sha256'], new['type_sha256'])
        self.assertNotEqual(old['dependencies'][NS + 'Pair'], new['dependencies'][NS + 'Pair'])

    def test_shared_witness_cannot_be_replaced_by_separate_witnesses(self):
        old, new = self.summary('witnessContext'), self.summary('witnessContext', self.changed_definition)
        self.assertEqual(old['type_sha256'], new['type_sha256'])
        self.assertNotEqual(old['dependencies'][NS + 'Shared'], new['dependencies'][NS + 'Shared'])

    def test_checker_fails_closed_on_missing_or_changed_evidence(self):
        expected = dict(result_id='R', theorem=NS + 'ordered', frozen_inputs=[], **self.summary('ordered'))
        result = {'id': 'R', 'theorem': NS + 'ordered'}
        with patch.object(contracts, 'contracts', return_value={'R': expected}):
            self.assertEqual(contracts.check(result, self.rows['ordered'], ROOT), [])
            self.assertEqual(contracts.check(result, self.rows['renamed'], ROOT), [])
            self.assertEqual(contracts.check(result, {}, ROOT)[0]['kind'], 'expression-contract-unavailable')
            self.assertEqual(contracts.check(result, self.rows['swapped'], ROOT)[0]['kind'], 'expression-contract-type')
            self.assertEqual(contracts.check(result, self.changed_definition['ordered'], ROOT)[0]['kind'], 'expression-contract-dependencies')

    def test_live_contract_is_requested_by_standard_binding_input(self):
        import corpus
        result_id = 'CATHOLICISM-STAGE2-CLASSICAL-ATTRIBUTES'
        result = json.loads((ROOT / 'corpus/results' / f'{result_id}.json').read_text())
        request = corpus.bind_tool_input([(ROOT, result)])
        self.assertEqual(request['contract_theorems'], [result['theorem']])
        # Saved legacy head-only descriptions can no longer pass this scope.
        problems = contracts.check(result, {}, ROOT)
        self.assertTrue(any(p['kind'] == 'expression-contract-unavailable' for p in problems))


if __name__ == '__main__':
    unittest.main()
