"""The Fourth-Way root's activated GOD_4 binding rejects trivial naming."""
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

import corpus
from lean_test_support import requires_built

ROOT = Path(__file__).resolve().parents[1]


@requires_built('TruthCore.Results.Case.Catholicism.FromQuartaViaWithClassicalAttributes.Solution')
class QuartaGodBindingTest(unittest.TestCase):
    def test_wrong_naming_despite_classical_conclusion(self):
        argument = json.loads((ROOT / 'corpus/arguments/CATHOLICISM-FROM-QUARTA-VIA-WITH-CLASSICAL-ATTRIBUTES.json').read_text())
        god = json.loads((ROOT / 'corpus/disambiguations/god.json').read_text())
        classical = next(s for s in god['senses'] if s['label'] == 'GOD_4')
        self.assertEqual(argument['term_senses']['GOD'], classical['id'])
        statements = {r['id']: r for _, r in corpus.load_dir('statements')}
        naming = next(r for r in statements.values() if r.get('legacy_id') == 'STMT-GOD-NAMES-THE-FULLY-DESCRIBED-PRINCIPLE')
        with tempfile.TemporaryDirectory() as temp:
            directory = Path(temp)
            command = ['python3', 'scripts/worker_env.py', '--']
            command += ['lean'] if os.environ.get('LEAN_PATH') else ['lake', 'env', 'lean']
            subprocess.run(command + ['-o', str(directory / 'QuartaGodBinding.olean'), 'scripts/fixtures/QuartaGodBinding.lean'], cwd=ROOT, check=True, capture_output=True, text=True)
            request = directory / 'request.json'
            request.write_text(json.dumps({'modules': ['QuartaGodBinding'], 'theorems': ['TruthCore.QuartaGodBindingFixture.wrongNaming'], 'sense_theorems': ['TruthCore.QuartaGodBindingFixture.wrongNaming'], 'sense_constants': [classical['lean_declaration']]}))
            env = dict(os.environ, LEAN_PATH=str(directory) + os.pathsep + os.environ.get('LEAN_PATH', ''))
            result = subprocess.run(command + ['--run', 'scripts/BindTypes.lean', str(request)], cwd=ROOT, env=env, check=True, capture_output=True, text=True)
            described = next(d for d in json.loads(result.stdout) if 'theorem' in d)
        constants = {'GOD': {s['id']: s['lean_declaration'] for s in god['senses']}}
        definition_senses = {s['definition_id']: {s['id']} for s in god['senses']}
        binding = {'premises': [{'hypothesis': 'hFull', 'statement_id': naming['id']} ]}
        problems = corpus.sense_bind_problems({}, argument, described, statements, constants, definition_senses, binding)
        self.assertEqual([(p['kind'], p.get('where')) for p in problems], [('statement-sense-not-instantiated', 'hFull')])
