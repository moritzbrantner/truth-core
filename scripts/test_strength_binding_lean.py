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
                'stronger': NS + 'Forward', 'weaker': NS + 'Forward', 'delta': NS + 'Delta', 'background': []}, statement_parameter_indices={role: [0, 1, 2] for role in ('stronger', 'weaker', 'delta')}),
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
        declarations = {'stronger': NS + 'Forward', 'weaker': NS + 'Forward', 'delta': NS + 'Delta', 'background': []}
        maps = {role: [0, 1, 2] for role in ('stronger', 'weaker', 'delta')}
        comparisons += [
            comparison('field-permuted', 'permuted', 'implication', 'swapped',
                       statement_declarations=declarations, statement_parameter_indices=maps),
            comparison('field-background', 'badBackground', 'implication', 'badBackgroundValid',
                       statement_declarations={**declarations, 'background': [NS + 'Background']},
                       statement_parameter_indices={**maps, 'background.0': [0, 1, 2]}),
            comparison('specialized', 'specialized', 'equivalence', 'specializedValid',
                       statement_declarations={'stronger': 'TruthCore.Greek.Plato.Timaeus.DistinctCausePrinciple',
                           'weaker': 'TruthCore.Greek.Plato.Timaeus.CausePrinciple',
                           'delta': 'TruthCore.Logic.Strength.Cause.SelfCausingGeneratedHaveAlternativeCause', 'background': []},
                       statement_parameter_indices={role: [0, 2, 3] for role in ('stronger', 'weaker', 'delta')}),
            comparison('poly-fields', 'polymorphic', 'implication', 'polymorphicCorrect',
                       statement_declarations={'stronger': NS + 'Universal', 'weaker': NS + 'Universal', 'background': []},
                       statement_parameter_indices={'stronger': [0, 1], 'weaker': [0, 1]}),
            comparison('padded', 'padded', 'equivalence', 'paddedValid',
                       statement_declarations={**declarations, 'weaker': NS + 'Delta', 'delta': NS + 'Padded'},
                       statement_parameter_indices=maps),
        ]
        padded = next(c for c in comparisons if c['id'] == 'padded')
        padded['certificates'] += [dict(role=role, theorem=NS + theorem) for role, theorem in [
            ('implication', 'paddedImplication'), ('delta_forward', 'paddedDeltaForward'),
            ('reconstruction', 'paddedReconstruction')]]
        request = directory / 'request.json'
        request.write_text(json.dumps({'modules': ['StrengthBindingFixture'], 'comparisons': comparisons}))
        env = dict(os.environ, LEAN_PATH=str(directory) + os.pathsep + os.environ.get('LEAN_PATH', ''))
        result = subprocess.run(run + ['lean', '--run', 'scripts/CheckStrength.lean', str(request)],
                                cwd=ROOT, env=env, check=True, capture_output=True, text=True)
        cls.rows = {r['id']: r for r in json.loads(result.stdout)}

    @classmethod
    def tearDownClass(cls):
        cls.temp.cleanup()

    def test_field_applications_reject_valid_but_misadvertised_certificates(self):
        for cid, fields in [('specialized', ['stronger', 'weaker', 'delta']),
                            ('field-permuted', ['stronger', 'weaker']),
                            ('field-background', ['background.0'])]:
            row = self.rows[cid]
            with self.subTest(cid=cid):
                self.assertTrue(all(c['bound'] for c in row['certificates']), row)
                self.assertFalse(row['bound'])
                for field in fields:
                    b = next(b for b in row['field_bindings'] if b['role'] == field)
                    self.assertFalse(b['bound'])
                    self.assertIn('expected', b['diagnostic'])
                    self.assertIn('actual', b['diagnostic'])
                # The live producer refuses these exact Lean responses before any
                # verifier run, report write, or displayed certified projection.
                import strength_comparisons as producer
                with self.assertRaises(ValueError):
                    producer.projection({'id': cid, 'comparison_spec': row['specification']}, {}, row, verified=True)
        self.assertTrue(self.rows['poly-fields']['bound'])

    def test_producer_writes_no_certified_bundle_for_rejected_fields(self):
        from unittest.mock import patch
        import strength_comparisons as producer
        import corpus
        for cid in ['specialized', 'field-permuted', 'field-background']:
            row = self.rows[cid]
            certificate = row['certificates'][0]
            relation = {'id': cid, 'comparison_spec': row['specification'],
                        'evidence_result_ids': {certificate['role']: 'RESULT'},
                        'subject_id': 'S', 'object_id': 'W', 'delta_statement_id': 'D',
                        'background_statement_ids': ['BG'] if cid == 'field-background' else [],
                        'statement_parameter_indices': {f['role']: f['parameter_indices'] for f in row['field_bindings']}}
            by_role = {f['role']: f['declaration'] for f in row['field_bindings']}
            data = {'comparisons': [relation], 'results': {'RESULT': {
                'id': 'RESULT', 'theorem': certificate['theorem'], 'solution_module': 'StrengthBindingFixture', 'argument_id': 'ARG'}},
                'arguments': {'ARG': {}}, 'statements': {sid: {'lean_declaration': by_role[role]} for sid, role in
                    [('S', 'stronger'), ('W', 'weaker'), ('D', 'delta')] + ([('BG', 'background.0')] if cid == 'field-background' else [])}}
            with tempfile.TemporaryDirectory() as directory, patch.object(producer, 'input_manifest', return_value={}), \
                 patch.object(producer, 'module_for', return_value='StrengthBindingFixture'), \
                 patch.object(producer, 'run') as run, \
                 patch.object(producer, 'json_tool', side_effect=[[], [row]]), \
                 patch.object(corpus, 'bind_result', return_value={'status': 'bound'}), \
                 patch.object(corpus, 'bind_tool_input', return_value={}):
                root = Path(directory)
                output = root / '.cache/report.json'
                with self.subTest(cid=cid), self.assertRaisesRegex(ValueError, 'application/background mismatch'):
                    producer.write_bundle(root, output, data)
                self.assertFalse(output.exists())
                self.assertFalse(any('scripts/verify-result.sh' in call.args[1] for call in run.call_args_list))

    def test_padding_factorization_does_not_certify_informativeness(self):
        self.assertTrue(self.rows['padded']['bound'])
        self.assertFalse(self.rows['padded']['delta_degenerate'])
        row = self.rows['padded']
        self.assertTrue(all(c['bound'] for c in row['certificates']))
        import strength_comparisons as producer
        fields = {f['role']: f for f in row['field_bindings']}
        relation = dict(id='padded', comparison_spec=row['specification'],
                        evidence_result_ids={c['role']: c['role'] for c in row['certificates']},
                        subject_id='S', object_id='W', delta_statement_id='D',
                        background_statement_ids=[], note='S padded with True',
                        statement_parameter_indices={role: f['parameter_indices'] for role, f in fields.items()})
        data = dict(results={c['role']: dict(theorem=c['theorem'], argument_id=c['role']) for c in row['certificates']},
                    statements={sid: dict(lean_declaration=fields[role]['declaration']) for sid, role in
                                [('S', 'stronger'), ('W', 'weaker'), ('D', 'delta')]}, definitions={}, disambiguations={})
        report = producer.projection(relation, data, row, verified=True)
        self.assertEqual(report['delta_status'], 'exact factorization proved')
        self.assertIn('not certified', report['explanatory_status'])

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
