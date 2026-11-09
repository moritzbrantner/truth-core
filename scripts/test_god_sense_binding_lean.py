"""Real elaboration control for the parameterized classical-God root binding."""
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

import corpus
from lean_test_support import requires_built

ROOT = Path(__file__).resolve().parents[1]
CLASSICAL = 'TruthCore.Case.Catholicism.Signature.IsGod'
SENSE = '52c2ebac-0a71-4dd4-8a21-804c1dd0847a'
HEAD = 'TruthCore.Case.Catholicism.GodIsMaximalInBeing'


@requires_built('TruthCore.Case.Catholicism.StageTwo')
class GodSenseBindingTest(unittest.TestCase):
    def test_same_head_different_instantiated_predicate(self):
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            command = ['python3', 'scripts/worker_env.py', '--', 'lake', 'env', 'lean']
            subprocess.run(command + ['-o', str(directory / 'GodSenseBinding.olean'),
                                     'scripts/fixtures/GodSenseBinding.lean'], cwd=ROOT,
                           check=True, capture_output=True, text=True)
            request = directory / 'input.json'
            names = ['TruthCore.GodSenseBindingFixture.' + name for name in ('classical', 'nominal')]
            request.write_text(json.dumps(dict(modules=['GodSenseBinding'], theorems=names,
                sense_theorems=names, sense_constants=[CLASSICAL], bundle_prefixes=[])))
            env = {**os.environ, 'LEAN_PATH': tmp + os.pathsep + os.environ.get('LEAN_PATH', '')}
            output = subprocess.run(command + ['--run', 'scripts/BindTypes.lean', str(request)],
                                    cwd=ROOT, env=env, check=True, capture_output=True, text=True)
            descriptions = [row for row in json.loads(output.stdout) if 'theorem' in row]
            self.assertEqual([row['theorem'] for row in descriptions], names)
        argument = {'term_senses': {'GOD': SENSE}, 'conclusion_statement_id': 'C'}
        statements = {'P': {'definition_ids': ['D']}, 'C': {'definition_ids': ['D']}}
        binding = {'premises': [{'hypothesis': 'h', 'statement_id': 'P'}], 'conclusion': {'statement_id': 'C'}}
        for description, expected in zip(descriptions, [[], ['h', 'result']]):
            self.assertEqual(description['result']['head'], HEAD)
            problems = corpus.sense_bind_problems({}, argument, description, statements,
                {'GOD': {SENSE: CLASSICAL}}, {'D': {SENSE}}, binding)
            self.assertEqual([p['where'] for p in problems], expected)
            self.assertTrue(all(p['kind'] == 'statement-sense-not-instantiated' for p in problems))
