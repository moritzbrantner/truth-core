"""Exact theorem-application binding, independent of proof-status presentation."""
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
NS = 'TruthCore.StrengthBindingFixture.'


@unittest.skipUnless(shutil.which('lake') or (Path.home() / '.elan/bin/lake').exists(), 'Lean integration requires lake')
class StrengthBindingTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temp = tempfile.TemporaryDirectory()
        directory = Path(cls.temp.name)
        run = ['python3', 'scripts/worker_env.py', '--', 'lake', 'env']
        subprocess.run(run + ['lean', '-o', str(directory / 'StrengthBindingFixture.olean'),
                              'scripts/fixtures/StrengthBinding.lean'], cwd=ROOT, check=True, capture_output=True, text=True)
        def comparison(cid, spec, role, theorem, **extra):
            return dict(id=cid, specification=NS + spec,
                        certificates=[dict(role=role, theorem=NS + theorem)], **extra)
        comparisons = [
            comparison('correct', 'selected', 'implication', 'correct', statement_declarations={
                'stronger': NS + 'Forward', 'weaker': NS + 'Forward', 'delta': NS + 'Delta', 'background': []}),
            comparison('swapped', 'selected', 'implication', 'swapped'),
            comparison('correct-bg', 'withBackground', 'implication', 'backgroundCorrect'),
            comparison('wrong-bg', 'withBackground', 'implication', 'backgroundWrong'),
            comparison('sufficient-only', 'sufficientOnly', 'delta_forward', 'reconstructionOnly'),
            comparison('unknown-role', 'selected', 'strictly_stronger', 'correct'),
            dict(id='degenerate', specification=NS + 'degenerate', certificates=[]),
            dict(id='separator', specification=NS + 'equality', certificates=[], separator={
                'setting': NS + 'separator', 'theorem': NS + 'separatorCorrect'}),
            dict(id='wrong-setting', specification=NS + 'equality', certificates=[], separator={
                'setting': NS + 'wrongSeparator', 'theorem': NS + 'separatorCorrect'}),
            dict(id='wrong-witness', specification=NS + 'equality', certificates=[], separator={
                'setting': NS + 'separator', 'theorem': NS + 'separatorSwapped'}),
            comparison('poly-correct', 'polymorphic', 'implication', 'polymorphicCorrect'),
            comparison('poly-wrong', 'polymorphic', 'implication', 'monomorphicOnly'),
        ]
        request = directory / 'request.json'
        request.write_text(json.dumps({'modules': ['StrengthBindingFixture'], 'comparisons': comparisons}))
        env = dict(os.environ, LEAN_PATH=str(directory) + os.pathsep + os.environ.get('LEAN_PATH', ''))
        result = subprocess.run(run + ['lean', '--run', 'scripts/CheckStrength.lean', str(request)],
                                cwd=ROOT, env=env, check=True, capture_output=True, text=True)
        cls.rows = {r['id']: r for r in json.loads(result.stdout)}

    @classmethod
    def tearDownClass(cls):
        cls.temp.cleanup()

    def test_exact_application_and_field_identity(self):
        self.assertTrue(self.rows['correct']['bound'])
        self.assertFalse(self.rows['swapped']['bound'])
        self.assertTrue(all(b['bound'] for b in self.rows['correct']['field_bindings']))
        self.assertIn('Forward P a b', self.rows['correct']['formulas']['stronger'])
        self.assertEqual(self.rows['correct']['certificates'][0]['axioms'], [])

    def test_background_is_not_replaced_by_another_assumption(self):
        self.assertTrue(self.rows['correct-bg']['bound'])
        self.assertFalse(self.rows['wrong-bg']['bound'])
        self.assertEqual(self.rows['correct-bg']['formulas']['background'], ['B'])

    def test_sufficiency_is_not_exact_extra_content(self):
        self.assertFalse(self.rows['sufficient-only']['bound'])
        self.assertTrue(self.rows['degenerate']['delta_degenerate'])
        self.assertFalse(self.rows['unknown-role']['bound'])

    def test_separator_binds_same_spec_and_complete_setting(self):
        self.assertTrue(self.rows['separator']['bound'])
        self.assertFalse(self.rows['wrong-setting']['bound'])
        self.assertFalse(self.rows['wrong-witness']['bound'])
        self.assertIn('equality false true', self.rows['separator']['separator']['application'])

    def test_universe_parameters_are_not_silently_specialized(self):
        self.assertTrue(self.rows['poly-correct']['bound'])
        self.assertFalse(self.rows['poly-wrong']['bound'])


if __name__ == '__main__':
    unittest.main()
