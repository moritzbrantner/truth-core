"""Conservative configuration pruning, shared semantics and verification boundary."""
import copy
import argparse
from contextlib import redirect_stdout
import io
import json
from itertools import combinations
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

from configurations import check_generated_axioms, generated_names, composition_source, certificate_source, configuration_report, implication_closure, validate_case, verify_case


class ConfigurationTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        (self.root / 'Fixture.lean').write_text('')
        self.statements = {sid: {'id': sid, 'lean_declaration': 'Fixture.' + sid} for sid in ['P', 'Q', 'R', 'S']}
        self.results = {rid: {'id': rid, 'argument_id': rid, 'solution_module': 'Fixture', 'theorem': 'Fixture.' + rid} for rid in ['CORE', 'LARGER', 'PQ', 'QR']}
        self.arguments = {
            'CORE': {'id': 'CORE', 'premise_statement_ids': ['P', 'Q'], 'conclusion_statement_id': 'False'},
            'LARGER': {'id': 'LARGER', 'premise_statement_ids': ['P', 'Q', 'R'], 'conclusion_statement_id': 'False'},
            'PQ': {'id': 'PQ', 'premise_statement_ids': ['P'], 'conclusion_statement_id': 'Q'},
            'QR': {'id': 'QR', 'premise_statement_ids': ['Q'], 'conclusion_statement_id': 'R'},
        }
        self.models = {mid: {'id': mid, 'vocabulary': 'V', 'lean_declaration': 'Fixture.model', 'bindings': {'W': 'Bool', 'I': 'Bool', 'F': 'Fixture.frame', 'present': 'Fixture.present', 'w': 'Bool.false'}, 'modules': ['Fixture'],
                            'evaluations': [{'statement_id': sid, 'arguments': ['W'], 'value': 'satisfies'} for sid in ids]}
                       for mid, ids in [('MP', ['P']), ('MQ', ['Q'])]}
        self.case = {'id': 'CONFIG-TEST', 'seed_statement_id': 'P',
                     'semantics': {'id': 'test', 'logic': 'constructive', 'frame': 'arbitrary', 'domain': 'fixed', 'identity': 'literal', 'vocabulary': 'V', 'permitted_axioms': [],
                                   'modules': ['Fixture'], 'parameter_order': ['W', 'I', 'F', 'present', 'w'], 'parameters': [{'name': 'W', 'type': 'Type'}, {'name': 'I', 'type': 'Type'}, {'name': 'F', 'type': 'TruthCore.Modal.Frame W'}, {'name': 'present', 'type': 'I → W → Prop'}, {'name': 'w', 'type': 'W'}], 'applications': {sid: ['W'] for sid in self.statements}},
                     'configurations': [{'id': 'core', 'statement_ids': ['P', 'Q']}, {'id': 'superset', 'statement_ids': ['P', 'Q', 'R']},
                                        {'id': 'control', 'statement_ids': ['P']}, {'id': 'unknown', 'statement_ids': ['S']}],
                     'incompatibility_result_ids': ['LARGER', 'CORE'], 'implication_result_ids': [],
                     'model_bindings': [{'model_id': mid, 'parameters': {role: role for role in ['W', 'I', 'F', 'present', 'w']}} for mid in self.models]}

    def validate(self):
        validate_case(self.case, self.statements, self.results, self.arguments, self.models, self.root)

    def report(self, verified=True):
        return configuration_report(self.case, self.results, self.arguments, self.models, verified=verified)

    def test_core_prunes_supersets_not_subsets_and_minimality_has_removal_evidence(self):
        self.validate()
        report = {entry['id']: entry for entry in self.report()['configurations']}
        self.assertEqual(report['core']['status'], 'verified incompatible')
        self.assertEqual(report['superset']['incompatible_cores'][0]['result_id'], 'CORE')
        self.assertEqual(report['control']['status'], 'model witnessed')
        self.assertEqual(report['unknown']['status'], 'unresolved')
        core = report['core']['incompatible_cores'][0]
        self.assertIn('inclusion-minimal (each single removal', core['minimality'])
        self.assertEqual(core['removal_evidence'], [{'removed_statement_id': 'P', 'model_ids': ['MQ']}, {'removed_statement_id': 'Q', 'model_ids': ['MP']}])
        del self.models['MQ']
        self.case['model_bindings'] = [self.case['model_bindings'][0]]
        self.assertIn('minimal among supplied incompatibility certificates', self.report()['configurations'][1]['incompatible_cores'][0]['minimality'])

    def test_no_verification_no_certified_status_and_inconsistent_sets_have_no_discoveries(self):
        self.assertEqual({entry['status'] for entry in self.report(False)['configurations']}, {'verification required'})
        core = next(entry for entry in self.report()['configurations'] if entry['id'] == 'core')
        self.assertIsNone(core['consequences'])

    def test_profile_bindings_are_exact_and_do_not_coerce_vocabulary_or_assignment(self):
        for mutate in [lambda: self.models['MP'].update(vocabulary='Other'),
                       lambda: self.models['MP']['evaluations'][0].update(arguments=[]),
                       lambda: self.case['semantics'].update(identity=''),
                       lambda: self.case.update(status='verified incompatible'),
                       lambda: self.case['semantics']['parameters'][0].update(type='Type) := by trivial')]:
            saved_case, saved_models = copy.deepcopy(self.case), copy.deepcopy(self.models)
            mutate()
            with self.assertRaises(ValueError):
                self.validate()
            self.case, self.models = saved_case, saved_models

    def test_certificate_type_uses_same_explicit_parameters_and_false(self):
        source = certificate_source(self.case, self.statements, self.results, self.arguments)
        self.assertIn('(@Fixture.P W) → (@Fixture.Q W) → False := by', source)
        self.assertIn('exact @Fixture.CORE W I F present w', source)
        self.assertNotIn('sorry', source)

    def test_live_verifier_rebuilds_before_comparator_and_failure_emits_no_success(self):
        self.case['model_bindings'] = []
        calls = []
        def run(command, **kwargs):
            calls.append(command)
            output = ''
            if command[:3] == ['lake', 'env', 'lean']:
                source = Path(command[-1]).read_text()
                output = '\n'.join(f"'ConfigurationCertificates.{name}' does not depend on any axioms" for name in generated_names(source))
            return subprocess.CompletedProcess(command, 0, output, '')
        with patch('configurations.subprocess.run', side_effect=run):
            verification = verify_case(self.case, self.statements, self.results, self.arguments, self.models, self.root)
        self.assertEqual(calls[0], ['lake', 'build', 'Fixture'])
        self.assertEqual(calls[-1], ['scripts/verify-result.sh', 'LARGER'])
        self.assertEqual(verification['result_ids'], ['CORE', 'LARGER'])
        with patch('configurations.subprocess.run', return_value=subprocess.CompletedProcess([], 1, 'stale certificate', '')), self.assertRaisesRegex(ValueError, 'stale certificate'):
            verify_case(self.case, self.statements, self.results, self.arguments, self.models, self.root)
        self.assertEqual(list(self.root.glob('tmp*.lean')), [])

    def test_fixed_carrier_profile_excludes_and_reports_bool_models(self):
        self.case['semantics']['constants'] = {'W': 'Nat', 'I': 'Bool'}
        self.case['semantics']['parameters'] = [{'name': 'F', 'type': 'TruthCore.Modal.Frame Nat'}, {'name': 'present', 'type': 'Bool → Nat → Prop'}, {'name': 'w', 'type': 'Nat'}]
        self.validate()
        report = self.report()
        self.assertEqual(len(report['inapplicable_models']), 2)
        self.assertEqual(report['inapplicable_models'][0]['profile_mismatches'][0],
                         {'parameter': 'W', 'expected': 'Nat', 'registered': 'Bool'})
        control = next(entry for entry in report['configurations'] if entry['id'] == 'control')
        self.assertEqual(control['status'], 'unresolved')
        self.assertEqual(control['model_ids'], [])

    def test_same_vocabulary_models_cannot_be_hidden_to_manufacture_unknown(self):
        self.case['model_bindings'].pop()
        with self.assertRaisesRegex(ValueError, 'omits registered models'):
            self.validate()

    def test_proof_parameters_cannot_hide_an_original_premise(self):
        self.case['semantics']['parameters'].append({'name': 'hidden', 'type': 'Fixture.P W'})
        self.case['semantics']['parameter_order'].append('hidden')
        self.arguments['PQ']['premise_statement_ids'] = []
        self.case['implication_result_ids'] = ['PQ']
        with self.assertRaisesRegex(ValueError, 'semantic role'):
            self.validate()
        self.case['semantics']['parameters'].pop()
        self.case['semantics']['parameter_order'].pop()
        self.case['semantics']['parameters'][-1]['type'] = 'Fixture.P W'
        with self.assertRaisesRegex(ValueError, 'proof-valued parameters'):
            self.validate()

    def test_predicate_profiles_share_carriers_and_reject_unbound_or_proof_roles(self):
        # A non-Kripke profile (#576): carriers, then predicates over them.
        roles = ['Being', 'Respect', 'MovedIn', 'CanBe']
        self.case['semantics']['parameters'] = [{'name': 'Being', 'type': 'Type'}, {'name': 'Respect', 'type': 'Type'},
                                                {'name': 'MovedIn', 'type': 'Being → Respect → Prop'}, {'name': 'CanBe', 'type': 'Being → Respect → Prop'}]
        self.case['semantics']['parameter_order'] = roles
        self.case['semantics']['applications'] = {sid: ['Being', 'Respect', 'MovedIn'] for sid in self.statements}
        for model in self.models.values():
            model['bindings'] = {role: 'Fixture.' + role for role in roles}
            for evaluation in model['evaluations']:
                evaluation['arguments'] = ['Being', 'Respect', 'MovedIn']
        self.case['model_bindings'] = [{'model_id': mid, 'parameters': {role: role for role in roles}} for mid in self.models]
        self.validate()
        self.assertIn('exact @Fixture.CORE Being Respect MovedIn CanBe', certificate_source(self.case, self.statements, self.results, self.arguments))
        for bad in ['Respect → Being → Bool', 'Fixture.P Being', 'Prop', 'Later → Prop']:
            saved = copy.deepcopy(self.case)
            self.case['semantics']['parameters'][2]['type'] = bad
            with self.assertRaisesRegex(ValueError, 'proof-valued parameters'):
                self.validate()
            self.case = saved
        # A carrier is usable only after it is declared.
        self.case['semantics']['parameters'][0], self.case['semantics']['parameters'][2] = self.case['semantics']['parameters'][2], self.case['semantics']['parameters'][0]
        with self.assertRaisesRegex(ValueError, 'proof-valued parameters'):
            self.validate()

    def test_fixed_carriers_cannot_turn_world_or_roster_roles_into_proofs(self):
        self.case['semantics']['constants'] = {'W': 'False'}
        self.case['semantics']['parameters'] = [p for p in self.case['semantics']['parameters'] if p['name'] != 'W']
        with self.assertRaisesRegex(ValueError, 'proposition-valued carriers'):
            self.validate()

    def test_existence_psr_data_role_preserves_explicit_premises(self):
        profile = self.case['semantics']
        profile['parameters'].append({'name': 'Model', 'type': 'TruthCore.Explanation.ExistencePSR.Model W I'})
        profile['parameter_order'].append('Model')
        for mid, model in self.models.items():
            model['bindings']['Model'] = 'Fixture.model'
            self.case['model_bindings'][list(self.models).index(mid)]['parameters']['Model'] = 'Model'
        self.validate()
        source = certificate_source(self.case, self.statements, self.results, self.arguments, self.models)
        self.assertIn('(Model : TruthCore.Explanation.ExistencePSR.Model W I)', source)
        self.assertIn('def model_parameter_0_5 : TruthCore.Explanation.ExistencePSR.Model (Bool) (Bool) := Fixture.model', source)
        self.assertIn('(@Fixture.P W) → (@Fixture.Q W) → False', source)
        self.assertIn('exact @Fixture.CORE W I F present w Model', source)
        for bad in ['TruthCore.Explanation.ExistencePSR.Model W Later',
                    'TruthCore.Explanation.ExistencePSR.Model W',
                    'TruthCore.Explanation.ExistencePSR.Model W I Prop',
                    'Fixture.ProofBearingModel W I',
                    'TruthCore.Explanation.ExistencePSR.Sound m']:
            profile['parameters'][-1]['type'] = bad
            with self.assertRaisesRegex(ValueError, 'proof-valued parameters'):
                self.validate()

    def test_false_conclusions_cannot_enter_implication_discovery(self):
        self.statements['False'] = {'id': 'False', 'lean_declaration': 'TruthCore.Logic.ConfigurationFalse'}
        self.case['semantics']['applications']['False'] = []
        self.case['incompatibility_result_ids'] = []
        self.case['implication_result_ids'] = ['CORE']
        with self.assertRaisesRegex(ValueError, 'False-concluding'):
            self.validate()

    def test_specialized_constants_and_generated_proofs_obey_profile_axioms(self):
        source = 'theorem example : True := by trivial'
        for output in ['', "'ConfigurationCertificates.example' depends on axioms: [sorryAx]",
                       "'ConfigurationCertificates.example' depends on axioms: [Classical.choice]"]:
            with self.assertRaises(ValueError):
                check_generated_axioms(output, source, 'ConfigurationCertificates', [])
        check_generated_axioms("'ConfigurationCertificates.example' does not depend on any axioms", source, 'ConfigurationCertificates', [])
        check_generated_axioms("'ConfigurationCertificates.example' depends on axioms: [Classical.choice]", source, 'ConfigurationCertificates', ['Classical.choice'])
        self.case['semantics']['permitted_axioms'] = ['sorryAx']
        with self.assertRaisesRegex(ValueError, 'permitted_axioms'):
            self.validate()

    def test_overlap_is_a_verification_defect(self):
        self.models['MP']['evaluations'].append({'statement_id': 'Q', 'arguments': ['W'], 'value': 'satisfies'})
        with self.assertRaisesRegex(ValueError, 'verification defect'):
            self.report()

    def test_composition_tracks_exact_supports_and_cycles_cannot_introduce_atoms(self):
        self.case['implication_result_ids'] = ['PQ', 'QR']
        closure = implication_closure({'P', 'S'}, self.case, self.results, self.arguments)
        self.assertEqual(closure['items'][1]['statement_id'], 'R')
        self.assertEqual(closure['items'][1]['sufficient_subsets'][0]['statement_ids'], ['P'])
        self.assertEqual(closure['items'][1]['sufficient_subsets'][0]['result_ids'], ['PQ', 'QR'])
        self.assertEqual(implication_closure({'S'}, self.case, self.results, self.arguments)['items'], [])
        self.assertTrue(implication_closure({'P'}, self.case, self.results, self.arguments, limit=1)['truncated'])
        self.results['PQ']['transcription'] = 'single_application'
        with self.assertRaisesRegex(ValueError, 'transcription'):
            self.validate()

    def test_adding_a_certificate_changes_only_justified_statuses_and_order_is_stable(self):
        self.case['incompatibility_result_ids'] = []
        before = {item['id']: item['status'] for item in self.report()['configurations']}
        self.case['incompatibility_result_ids'] = ['CORE']
        after = {item['id']: item['status'] for item in self.report()['configurations']}
        self.assertEqual([key for key in before if before[key] != after[key]], ['core', 'superset'])
        report = self.report()
        self.case['configurations'].reverse()
        self.assertEqual(report, self.report())


class PersistentConfigurationRatchetTests(unittest.TestCase):
    def setUp(self):
        import corpus
        self.corpus = corpus
        self.statements = {r['id']: r for _, r in corpus.load_dir('statements')}
        self.results = {r['id']: r for _, r in corpus.load_dir('results')}
        self.arguments = {r['id']: r for _, r in corpus.load_dir('arguments')}
        self.models = {model['id']: model for model in corpus.registered_models()}
        self.cases = {case['id']: case for case in corpus.registered_configurations()}

    def report(self, case, selection=None):
        # Pure projection assumes the certificate gate; live CLI acceptance runs
        # that gate separately. This test is not itself Lean verification.
        return configuration_report(case, self.results, self.arguments, self.models, verified=True, selection=selection)

    def test_committed_ratchet_status_fixture_and_composed_core_provenance(self):
        fixture = json.loads((self.corpus.ROOT / 'scripts/testdata/configuration-ratchet.json').read_text())
        actual = {cid: {entry['id']: entry['status'] for entry in self.report(self.cases[cid])['configurations']} for cid in fixture}
        self.assertEqual(actual, fixture)
        case = self.cases['CONFIG-NECESSARY-INDIVIDUAL']
        report = self.report(case)
        composed = next(entry for entry in report['configurations'] if entry['id'] == 'composed-incompatible')
        core = composed['incompatible_cores'][0]
        self.assertEqual(len(core['result_ids']), 2)
        self.assertIn('inclusion-minimal', core['minimality'])
        source, count = composition_source(case, report, self.statements, self.results, self.arguments)
        self.assertGreater(count, 0)
        self.assertIn('have derived_', source)
        self.assertIn('@' + self.results[core['result_id']]['theorem'], source)

    def test_result_substitution_and_comparator_gate_disagreement_are_rejected(self):
        rid = 'NECESSARY-INDIVIDUAL-RE-TO-DICTO'
        result = self.results[rid]
        for replacement in [dict(theorem='sorryAx'), dict(comparator_config='results/OTHER/comparator.json'),
                            dict(solution_module='TruthCore.Case.Catholicism.StageOne.NecessaryIndividual.Quantifiers'),
                            dict(challenge_module='TruthCore.Case.Catholicism.StageOne.NecessaryIndividual.Quantifiers')]:
            with self.subTest(replacement=replacement), self.assertRaises(self.corpus.CorpusError):
                replaced = {**self.results, rid: {**result, **replacement}}
                self.corpus.registered_configurations(self.statements, replaced, self.arguments, self.models)

    def test_original_theorem_binding_rejects_erased_de_re_hypothesis(self):
        rid = 'NECESSARY-INDIVIDUAL-RE-TO-DICTO'
        result = self.results[rid]
        argument = {**self.arguments[result['argument_id']], 'premise_statement_ids': []}
        ni = 'TruthCore.Case.Catholicism.StageOne.NecessaryIndividual.'
        described = {'theorem': result['theorem'],
                     'binders': [{'name': 'h', 'prop': True, 'head': ni + 'DeRe', 'type': ni + 'DeRe F present w', 'wrappers': [], 'core_head': ni + 'DeRe'}],
                     'result': {'prop': True, 'head': ni + 'DeDicto', 'type': ni + 'DeDicto F present w', 'wrappers': [], 'core_head': ni + 'DeDicto'}}
        index = {sid: (self.corpus.ROOT, statement) for sid, statement in self.statements.items()}
        binding = self.corpus.bind_result(result, argument, index, described)
        self.assertEqual(binding['status'], 'mismatch')
        self.assertTrue(any(problem['kind'] == 'extra-hypothesis' for problem in binding['problems']))
        case = copy.deepcopy(self.cases['CONFIG-NECESSARY-INDIVIDUAL'])
        case['incompatibility_result_ids'] = []
        case['implication_result_ids'] = [rid]
        original_loader = self.corpus.load_dir
        def loader(kind):
            records = original_loader(kind)
            if kind == 'arguments':
                return [(path, argument if record['id'] == argument['id'] else record) for path, record in records]
            return records
        output = io.StringIO()
        args = argparse.Namespace(case=case['id'], seed=None, premise=[], registered=False, json=True)
        with patch.object(self.corpus, 'load_dir', side_effect=loader), \
             patch.object(self.corpus, 'registered_configurations', return_value=[case]), \
             patch.object(self.corpus, 'verify_case', return_value={}), \
             patch.object(self.corpus, 'verify_compositions', return_value={'cores': 0}), \
             patch.object(self.corpus, 'run_bind_tool', return_value=[described]) as tool, \
             redirect_stdout(output), self.assertRaisesRegex(self.corpus.CorpusError, 'original theorem binding rejected'):
            self.corpus.command_configurations(args)
        self.assertEqual(tool.call_args.args[0]['theorems'], [result['theorem']])
        self.assertEqual(output.getvalue(), '')


    def test_multi_case_verification_binds_the_exact_unique_union_and_fails_closed(self):
        cases = [self.cases['CONFIG-NECESSARY-INDIVIDUAL'], self.cases['CONFIG-NIGHT-ACTUALIZATION']]
        selected = sorted({rid for case in cases for key in ('incompatibility_result_ids', 'implication_result_ids') for rid in case.get(key, [])})
        context = dict(statements=self.statements, results=self.results, arguments=self.arguments, models=self.models,
                       cases=[cases[0], copy.deepcopy(cases[0]), cases[1]])
        args = argparse.Namespace(case=None, seed=None, premise=[], registered=False)
        descriptions = [{'theorem': self.results[rid]['theorem']} for rid in selected]
        with patch.object(self.corpus, 'verify_case', side_effect=lambda *args: {}), \
             patch.object(self.corpus, 'verify_compositions', return_value={'cores': 0}), \
             patch.object(self.corpus, 'run_bind_tool', return_value=descriptions) as tool, \
             patch.object(self.corpus, 'bind_result', return_value={'status': 'bound'}):
            reports = self.corpus.collect_configuration_reports(args, context)
        self.assertEqual(len(reports), 3)
        self.assertEqual(tool.call_count, 1)
        self.assertEqual(tool.call_args.args[0]['theorems'], [self.results[rid]['theorem'] for rid in selected])
        for report, case in zip(reports, context['cases']):
            self.assertEqual(report['verification']['original_bound_result_ids'],
                             sorted(set(case.get('incompatibility_result_ids', []) + case.get('implication_result_ids', []))))
        def bind(result, argument, statements, description):
            return {'status': 'mismatch', 'problems': ['missing description']} if 'error' in description else {'status': 'bound'}
        with patch.object(self.corpus, 'verify_case', side_effect=lambda *args: {}), \
             patch.object(self.corpus, 'verify_compositions', return_value={'cores': 0}), \
             patch.object(self.corpus, 'run_bind_tool', return_value=descriptions[:-1]), \
             patch.object(self.corpus, 'bind_result', side_effect=bind), \
             self.assertRaisesRegex(self.corpus.CorpusError, 'original theorem binding rejected'):
            self.corpus.collect_configuration_reports(args, context)

    def test_all_sixteen_positive_starter_subsets_match_independent_reference(self):
        case = self.cases['CONFIG-NECESSARY-INDIVIDUAL']
        prefix = 'STMT-NECESSARY-INDIVIDUAL-'
        re_, dicto, contingency, joint = [prefix + suffix for suffix in ['DE-RE', 'DE-DICTO', 'INDIVIDUAL-CONTINGENCY', 'JOINT-ABSENCE']]
        atoms = [re_, dicto, contingency, joint]
        # Exhaustion is only a small test oracle over syntactic input selections;
        # the production classifier composes cores and never enumerates 2^n.
        for size in range(5):
            for subset in combinations(atoms, size):
                incompatible = ((dicto in subset and joint in subset)
                                or (re_ in subset and contingency in subset)
                                or (re_ in subset and joint in subset))
                entry = self.report(case, {'id': 'test', 'statement_ids': list(subset)})['configurations'][0]
                self.assertEqual(entry['status'], 'verified incompatible' if incompatible else 'model witnessed', subset)
                self.assertFalse(entry['core_composition']['truncated'])

    def test_nat_profile_cannot_borrow_bool_satisfiability_or_minimality(self):
        case = self.cases['CONFIG-NECESSARY-INDIVIDUAL-NAT-WORLDS']
        report = self.report(case)
        self.assertEqual(len(report['inapplicable_models']), 3)
        self.assertEqual(report['configurations'][0]['status'], 'unresolved')
        selection = {'id': 'core', 'statement_ids': ['STMT-NECESSARY-INDIVIDUAL-DE-DICTO', 'STMT-NECESSARY-INDIVIDUAL-JOINT-ABSENCE']}
        core = self.report(case, selection)['configurations'][0]['incompatible_cores'][0]
        self.assertIn('minimal among supplied incompatibility certificates', core['minimality'])
        self.assertTrue(all(not item['model_ids'] for item in core['removal_evidence']))
        source = certificate_source(case, self.statements, self.results, self.arguments, self.models)
        self.assertIn(' Nat Bool F present w', source)
        self.assertNotIn('model_parameter_', source)


if __name__ == '__main__':
    unittest.main()
