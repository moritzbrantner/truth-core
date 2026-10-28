"""Canonical bounded families and freshness checks for disposable verified outputs."""
import copy
import argparse
from contextlib import redirect_stdout
import io
import os
import json
from pathlib import Path
import tempfile
from unittest.mock import patch
from itertools import combinations
import unittest

import corpus
from configuration_explorer import INPUT_FILES, MAX_DIMENSIONS, bounded_family, build_case_spaces, input_manifest, read_bundle, write_bundle
from configurations import configuration_report, model_profile_mismatches


class ConfigurationExplorerTests(unittest.TestCase):
    def setUp(self):
        self.context = corpus.configuration_context()
        self.reports = []
        for case in self.context['cases']:
            report = configuration_report(case, self.context['results'], self.context['arguments'], self.context['models'], verified=True)
            ids = sorted(case['incompatibility_result_ids'] + case['implication_result_ids'])
            models = [self.context['models'][entry['model_id']] for entry in case['model_bindings'] if not model_profile_mismatches(case, entry, self.context['models'])]
            report['verification'] = {'result_ids': ids, 'original_bound_result_ids': ids,
                                      'compositions': {'cores': sum(len(entry['incompatible_cores']) for entry in report['configurations'])},
                                      'models': {'models': len(models), 'certificates': sum(1 + len(model['carriers']) + len(model['evaluations']) for model in models), 'axioms': []}}
            self.reports.append(report)

    def classify(self, case, selected):
        return configuration_report(case, self.context['results'], self.context['arguments'], self.context['models'], verified=True,
                                    selection={'id': 'selection', 'statement_ids': selected})['configurations'][0]

    def test_pruned_families_match_every_bounded_selection_without_browser_logic(self):
        for case in self.context['cases']:
            space = bounded_family(case, lambda ids: self.classify(case, ids))
            nodes = {node['id']: node for node in space['nodes']}
            dimensions = space['statement_ids']
            selections = 2 ** len(dimensions)
            self.assertEqual(space['limits']['covered_selections'], selections)
            self.assertLess(space['limits']['classifier_calls'], selections)
            self.assertLess(space['limits']['terminal_families'], selections)
            for count in range(len(dimensions) + 1):
                for selected in combinations(dimensions, count):
                    node = nodes[space['root']]
                    while node['kind'] == 'decision':
                        node = nodes[node['include'] if node['statement_id'] in selected else node['exclude']]
                    self.assertEqual(node['report']['status'], self.classify(case, list(selected))['status'], selected)
                    self.assertTrue(set(node['required_statement_ids']) <= set(selected))
                    self.assertTrue(set(selected) <= set(node['required_statement_ids'] + node['optional_statement_ids']))
                    if node['report']['status'] == 'verified incompatible':
                        self.assertIsNone(node['report']['consequences'])

    def test_unverified_data_and_over_limit_dimensions_are_rejected(self):
        reports = copy.deepcopy(self.reports)
        reports[0]['verified'] = False
        with self.assertRaisesRegex(ValueError, 'unverified'):
            build_case_spaces(self.context, reports)
        case = copy.deepcopy(self.context['cases'][0])
        case['semantics']['applications'] = {f'DIMENSION_{i}': [] for i in range(MAX_DIMENSIONS + 1)}
        with self.assertRaisesRegex(ValueError, f'at most {MAX_DIMENSIONS}'):
            bounded_family(case, lambda ids: self.fail('over-limit inputs must fail before classification'))

    def test_build_preflight_is_explicit_and_cannot_bypass_missing_or_uncached_inputs(self):
        args = argparse.Namespace(build_input=True, check=None, output=None, json=False)
        with patch.dict(os.environ, {}, clear=True), redirect_stdout(io.StringIO()) as output:
            self.assertEqual(corpus.command_configuration_report(args), 0)
            self.assertIn('registered-only', output.getvalue())
        for environment in [{'TRUTH_CORE_REQUIRE_CONFIGURATION_REPORT': 'true'},
                            {'TRUTH_CORE_CONFIGURATION_REPORT': '/tmp/unsupported-cache-input.json'}]:
            with patch.dict(os.environ, environment, clear=True), self.assertRaises(corpus.CorpusError):
                corpus.command_configuration_report(args)

    def report_root(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        root = Path(directory.name)
        for relative in INPUT_FILES:
            path = root / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text('fixed input', encoding='utf-8')
        return root

    def write_test_bundle(self, root):
        def replay(case, report, *args):
            return {'cores': sum(len(entry['incompatible_cores']) for entry in report['configurations'])}
        with patch('configuration_explorer.source_head', return_value='test-head'), \
             patch('configuration_explorer.verify_compositions', side_effect=replay) as gate:
            bundle = write_bundle(root, root / '.cache/report.json', self.context, self.reports, input_manifest(root))
        self.assertEqual(gate.call_count, len(self.reports))
        return bundle

    def test_atomic_output_roundtrip_and_missing_stale_or_unverified_reports_fail(self):
        root = self.report_root()
        path = root / '.cache/report.json'
        with self.assertRaisesRegex(ValueError, 'cannot read'):
            read_bundle(root, path, self.context)
        bundle = self.write_test_bundle(root)
        with patch('configuration_explorer.source_head', return_value='test-head'):
            self.assertEqual(read_bundle(root, path, self.context), bundle)
            for mutate in [lambda item: item['producer'].update(mode='registered'),
                           lambda item: item['producer'].update(trust='unsupported success claim'),
                           lambda item: item['cases'][0].update(verified=False),
                           lambda item: item['cases'][0]['verification'].update(original_bound_result_ids=[]),
                           lambda item: next(case for case in item['cases'] if case['verification']['models']['models'])['verification'].update(models={'models': 0, 'certificates': 0, 'axioms': []}),
                           lambda item: item['cases'][0]['assumption_space']['nodes'][0].update(include='invented')]:
                malformed = copy.deepcopy(bundle)
                mutate(malformed)
                path.write_text(json.dumps(malformed), encoding='utf-8')
                with self.assertRaises(ValueError):
                    read_bundle(root, path, self.context)
            path.write_text(json.dumps(bundle), encoding='utf-8')
            (root / 'scripts/configurations.py').write_text('changed input', encoding='utf-8')
            with self.assertRaisesRegex(ValueError, 'stale'):
                read_bundle(root, path, self.context)

    def test_input_manifest_ignores_ui_style_but_binds_proof_tooling_and_models(self):
        root = self.report_root()
        before = input_manifest(root)
        (root / 'docs').mkdir()
        (root / 'docs/note.md').write_text('unrelated prose', encoding='utf-8')
        self.assertEqual(input_manifest(root), before)
        model = root / 'corpus/models/new.json'
        model.parent.mkdir(parents=True)
        model.write_text('{}', encoding='utf-8')
        self.assertNotEqual(input_manifest(root), before)

    def test_changed_inputs_never_replace_previous_output_or_leave_partial_file(self):
        root = self.report_root()
        self.write_test_bundle(root)
        path = root / '.cache/report.json'
        previous = path.read_bytes()
        initial = input_manifest(root)
        def changed_replay(case, report, *args):
            (root / 'scripts/configurations.py').write_text('changed during proof', encoding='utf-8')
            return {'cores': sum(len(entry['incompatible_cores']) for entry in report['configurations'])}
        with patch('configuration_explorer.verify_compositions', side_effect=changed_replay), self.assertRaisesRegex(ValueError, 'changed during'):
            write_bundle(root, path, self.context, self.reports, initial)
        self.assertEqual(path.read_bytes(), previous)
        self.assertEqual(list(path.parent.iterdir()), [path])
        with self.assertRaisesRegex(ValueError, '.cache'):
            write_bundle(root, root / 'tracked.json', self.context, self.reports, initial)

    def test_bundles_are_deterministic_and_decisions_do_not_claim_metaphysical_counts(self):
        first = build_case_spaces(self.context, self.reports)
        second = build_case_spaces(self.context, self.reports)
        self.assertEqual(first, second)
        self.assertIn('not philosophically distinct theories', first[0]['assumption_space']['limits']['note'])


if __name__ == '__main__':
    unittest.main()
