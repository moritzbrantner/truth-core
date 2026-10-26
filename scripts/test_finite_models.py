"""Finite-model lookup is exact, conservative about missing evaluations, and certified."""
import copy
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import corpus
from finite_models import certificate_source, model_report, validate_model, verify_models


class FiniteModelsTests(unittest.TestCase):
    def setUp(self):
        self.models = corpus.registered_models()
        self.statements = {r['id']: r for _, r in corpus.load_dir('statements')}
        self.model = next(m for m in self.models if m['id'] == 'MODEL-ACT-POTENCY-M3')

    def test_every_backfilled_family_is_explicit_and_locally_well_formed(self):
        self.assertEqual(len({m['id'] for m in self.models}), len(self.models))
        for family in ['Q11-', 'ACT-POTENCY-', 'ORDER-', 'PHYSICS-', 'PSR-', 'SCOTT-']:
            self.assertTrue(any(m['id'].startswith('MODEL-' + family) for m in self.models))
        for model in self.models:
            validate_model(model, self.statements, corpus.ROOT)

    def test_modal_quantifier_shift_controls_share_premises_but_diverge_on_target(self):
        models = {m['id']: {e['statement_id']: e['value'] for e in m['evaluations']}
                  for m in self.models}
        psr_stable = models['MODEL-PSR-INTRINSIC']
        psr_variable = models['MODEL-PSR-WORLDWISE-ALTERNATING']
        for premise in ['STMT-PSR-SOUND-COMPONENT', 'STMT-PSR-EXISTENCE-COMPONENT',
                        'STMT-KANT-CONVERSION-NECESSARY-WITNESS']:
            self.assertEqual((psr_stable[premise], psr_variable[premise]), ('satisfies', 'satisfies'))
        self.assertEqual(psr_stable['STMT-MODAL-EXPLANATION-STABLE'], 'satisfies')
        self.assertEqual(psr_variable['STMT-MODAL-EXPLANATION-STABLE'], 'violates')

        fixed = models['MODEL-MODAL-FIXED-EFFECT']
        variable = models['MODEL-MODAL-VARIABLE-EFFECTS']
        for premise in ['STMT-MODAL-SOUND-DISTINCT-CAUSES',
                        'STMT-KANT-CONVERSION-NECESSARY-WITNESS',
                        'STMT-MODAL-NECESSARY-AT-INDIVIDUAL',
                        'STMT-MODAL-NECESSARY-CAUSES-SOMETHING']:
            self.assertEqual((fixed[premise], variable[premise]), ('satisfies', 'satisfies'))
        self.assertEqual(fixed['STMT-MODAL-SAME-NECESSARY-EFFECT'], 'satisfies')
        self.assertEqual(variable['STMT-MODAL-SAME-NECESSARY-EFFECT'], 'violates')
        self.assertEqual(fixed['STMT-KANT-CONTINGENT-INDIVIDUAL'], 'violates')
        self.assertEqual(variable['STMT-KANT-CONTINGENT-INDIVIDUAL'], 'satisfies')

    def test_explained_source_omission_controls_keep_population_separate_from_well_foundedness(self):
        models = {m['id']: {e['statement_id']: e['value'] for e in m['evaluations']}
                  for m in self.models}
        source = models['MODEL-PSR-INTRINSIC']
        mutual = models['MODEL-PSR-MUTUAL-CAUSES']
        empty = models['MODEL-PSR-EMPTY-WORLD']
        psr = 'STMT-PSR-EXISTENCE-COMPONENT'
        populated = 'STMT-PSR-POPULATED-AT'
        well_founded = 'STMT-PSR-WELL-FOUNDED-CAUSES-AT'
        explained = 'STMT-PSR-EXPLAINED-SOURCE-AT'
        external = 'STMT-PSR-EXTERNAL-CAUSE-COMPONENT'
        self.assertTrue(all(m[psr] == 'satisfies' for m in (source, mutual, empty)))
        self.assertEqual((source[populated], source[well_founded], source[explained], source[external]),
                         ('satisfies', 'satisfies', 'satisfies', 'violates'))
        self.assertEqual((mutual[populated], mutual[well_founded], mutual[explained], mutual[external]),
                         ('satisfies', 'violates', 'violates', 'satisfies'))
        self.assertEqual((empty[populated], empty[well_founded], empty[external]),
                         ('violates', 'satisfies', 'satisfies'))
        report = model_report([next(m for m in self.models if m['id'] == 'MODEL-PSR-MUTUAL-CAUSES')],
                              explained, [populated, psr, well_founded])
        self.assertEqual(report['models'][0]['classification'], 'incomplete_or_inapplicable')
        self.assertEqual(report['models'][0]['violated_premises'], [well_founded])

    def test_unknown_premises_and_unrelated_models_cannot_be_counterexamples(self):
        target = 'STMT-ACT-SIMPLY-PRIOR-TO-POTENCY'
        # Choose a genuinely registered satisfied premise without relying on its name.
        premise = next(e['statement_id'] for e in self.model['evaluations'] if e['value'] == 'satisfies')
        report = model_report([self.model], target, [premise])
        self.assertEqual(report['models'][0]['classification'], 'counterexample')
        self.assertEqual(report['premise_statement_ids'], [premise])
        self.assertEqual(model_report([self.model], target, ['UNKNOWN'])['models'][0]['classification'], 'incomplete_or_inapplicable')
        self.assertEqual(model_report([self.model], target, [target])['models'][0]['classification'], 'incomplete_or_inapplicable')
        self.assertEqual(model_report([self.model], 'UNKNOWN')['models'], [])

    def test_cofailure_requires_identical_complete_coverage_nonempty_failure_and_vocabulary(self):
        def model(mid, vocab, values):
            return dict(id=mid, vocabulary=vocab, evaluations=[dict(statement_id=k, value=v) for k, v in values.items()])
        a = model('A', 'V', {'P': 'violates', 'Q': 'violates'})
        b = model('B', 'V', {'P': 'satisfies', 'Q': 'satisfies'})
        patterns = model_report([a, b])['cofailure_candidates']
        self.assertEqual(patterns, [dict(statement_ids=['P', 'Q'], vocabulary='V', model_ids=['A', 'B'], cofailure_model_ids=['A'], status='candidate_only')])
        for extra in [model('C', 'V', {'P': 'satisfies'}), model('C', 'V', {'P': 'satisfies', 'Q': 'violates'})]:
            self.assertEqual(model_report([a, b, extra])['cofailure_candidates'], [])
        self.assertEqual(model_report([b])['cofailure_candidates'], [])
        self.assertEqual(model_report([a, model('B', 'OTHER', {'P': 'violates'})])['cofailure_candidates'][0]['model_ids'], ['A'])

    def test_validation_rejects_unbound_references_conflicts_and_lean_injection(self):
        changes = [dict(id='BAD'), dict(modules=['Missing.Module']), dict(modules=[{}]), dict(bindings={'X': 'False) := by trivial\n--'}),
                   dict(carriers=[]), dict(carriers=[{**self.model['carriers'][0], 'elements': [{}]}]), dict(evaluations=[]), dict(evaluations=[3]),
                   dict(evaluations=[{**self.model['evaluations'][0], 'statement_id': 'UNKNOWN'}]),
                   dict(evaluations=[{**self.model['evaluations'][0], 'arguments': ['unknown']}]),
                   dict(evaluations=[{**self.model['evaluations'][0], 'theorem': 'by trivial'}]),
                   dict(evaluations=self.model['evaluations'] + [self.model['evaluations'][0]])]
        for change in changes:
            with self.subTest(change=change), self.assertRaises(ValueError):
                validate_model({**self.model, **change}, self.statements, corpus.ROOT)

    def test_certificate_checks_exact_statement_arguments_negation_carrier_and_axioms(self):
        source, names = certificate_source([self.model], self.statements)
        self.assertIn('@' + self.statements['STMT-ACT-SIMPLY-PRIOR-TO-POTENCY']['lean_declaration'], source)
        self.assertIn('¬ (@', source)
        self.assertIn(self.model['bindings']['PriorSimply'], source)
        self.assertIn('∀ x : (', source)
        self.assertIn('#print axioms interpretation_0', source)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            with patch('finite_models.subprocess.run', return_value=subprocess.CompletedProcess([], 0, '\n'.join(f"'FiniteModelCertificates.{name}' does not depend on any axioms" for name in names), '')):
                self.assertEqual(verify_models([self.model], self.statements, root)['axioms'], [])
            for output in ['', "'FiniteModelCertificates.interpretation_0' depends on axioms: [sorryAx]"]:
                with patch('finite_models.subprocess.run', return_value=subprocess.CompletedProcess([], 0, output, '')), self.assertRaises(ValueError):
                    verify_models([self.model], self.statements, root)
            with patch('finite_models.subprocess.run', return_value=subprocess.CompletedProcess([], 1, 'type mismatch', '')), self.assertRaises(ValueError):
                verify_models([self.model], self.statements, root)
            self.assertEqual(list(root.iterdir()), [])

    def test_cli_unknown_statement_and_argument_fail_before_verification(self):
        for args in [['--check', 'UNKNOWN'], ['--argument', 'UNKNOWN']]:
            result = subprocess.run(['python3', str(corpus.ROOT / 'scripts/corpus.py'), 'models', *args], capture_output=True, text=True)
            self.assertEqual(result.returncode, 2)
            self.assertIn('unknown', result.stderr)

    def test_dossier_shows_exact_evaluation_without_affecting_frontier(self):
        from premise_dossiers import dossier_index
        directories = ['statements', 'claims', 'definitions', 'disambiguations', 'arguments', 'inferences', 'results', 'relations', 'attempts']
        data = {kind: [r for _, r in corpus.load_dir(kind)] for kind in directories}
        report = corpus.frontier_report(data['statements'], data['arguments'], data['results'], data['relations'], claims=data['claims'], transcription=corpus.transcription_flags(data['results'], data['arguments'], data['statements']))
        before = copy.deepcopy(report)
        data['models'] = self.models
        dossier = dossier_index(data, report)['STMT-ACT-SIMPLY-PRIOR-TO-POTENCY']
        self.assertEqual(report, before)
        self.assertFalse(dossier['established'])
        self.assertTrue(any(m['model_id'] == self.model['id'] and m['value'] == 'violates' for m in dossier['model_evaluations']))


if __name__ == '__main__':
    unittest.main()
