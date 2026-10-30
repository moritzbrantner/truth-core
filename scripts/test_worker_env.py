"""One-time worker preflight and literal command passthrough, without real tools."""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

import worker_env


class WorkerEnvironmentTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.cache = self.root / 'cache with spaces'
        self.pin = 'leanprover/lean4:v4.35.0'
        (self.root / 'lean-toolchain').write_text(self.pin + '\n')
        exporter = self.cache / 'lean4export/lean-toolchain'
        exporter.parent.mkdir(parents=True)
        exporter.write_text(self.pin + '\n')
        for name in worker_env.BINARIES:
            path = self.cache / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text('#!/bin/sh\nexit 0\n')
            path.chmod(0o700)
        self.inherited = {'HOME': str(self.root / 'home'), 'PATH': '/fixture/bin'}
        self.env = {**self.inherited, 'TRUTH_CORE_VERIFIER_HOME': str(self.cache)}

    def test_explicit_environment_precedes_local_config(self):
        with patch.object(worker_env, 'git') as git:
            env = worker_env.environment(self.root, self.env)
        git.assert_not_called()
        self.assertEqual(env['TRUTH_CORE_VERIFIER_HOME'], str(self.cache))
        self.assertEqual(env['PATH'], str(self.root / 'home/.elan/bin') + ':/fixture/bin')
        self.assertEqual(self.env['PATH'], '/fixture/bin')

    def test_local_config_precedes_default(self):
        with patch.object(worker_env, 'git', return_value=str(self.cache)) as git:
            env = worker_env.environment(self.root, self.inherited)
        git.assert_called_once_with(self.root, 'config', '--local', '--get',
                                    'truthcore.verifierHome', optional=True)
        self.assertEqual(env['TRUTH_CORE_VERIFIER_HOME'], str(self.cache))

    def test_default_and_empty_environment_override(self):
        with patch.object(worker_env, 'git', return_value=''):
            env = worker_env.environment(self.root, {**self.inherited,
                                                   'TRUTH_CORE_VERIFIER_HOME': ''})
        self.assertEqual(env['TRUTH_CORE_VERIFIER_HOME'],
                         str(self.root / 'home/.cache/truth-core-verifier'))

    def test_check_reports_exact_workspace_head_and_pin(self):
        with patch.object(worker_env, 'git', return_value='fixture-head'), \
                patch.object(worker_env.subprocess, 'check_output') as version:
            report = worker_env.check_environment(self.root, self.env)
        version.assert_not_called()
        self.assertEqual(report, {'workspace': str(self.root), 'head': 'fixture-head',
                                  'toolchain': self.pin, 'verifier_home': str(self.cache)})

    def test_rejects_mismatched_exporter(self):
        (self.cache / 'lean4export/lean-toolchain').write_text('leanprover/lean4:v4.34.0\n')
        with self.assertRaisesRegex(ValueError, 'differs from repository'):
            worker_env.check_environment(self.root, self.env)

    def test_rejects_missing_exporter_pin(self):
        (self.cache / 'lean4export/lean-toolchain').unlink()
        with self.assertRaises(FileNotFoundError):
            worker_env.check_environment(self.root, self.env)

    def test_requires_all_four_executable_files(self):
        for name in worker_env.BINARIES:
            with self.subTest(name=name):
                path = self.cache / name
                path.chmod(0o600)
                with self.assertRaisesRegex(ValueError, 'missing executable'):
                    worker_env.check_environment(self.root, self.env)
                path.chmod(0o700)
        (self.cache / worker_env.BINARIES[0]).unlink()
        with self.assertRaisesRegex(ValueError, 'missing executable'):
            worker_env.check_environment(self.root, self.env)

    def test_optional_lean_version_matches_release(self):
        with patch.object(worker_env, 'git', return_value='fixture-head'), \
                patch.object(worker_env.subprocess, 'check_output',
                             return_value='Lean (version 4.35.0, fixture)\n') as version:
            worker_env.check_environment(self.root, self.env, lean_version=True)
        version.assert_called_once_with(['elan', 'run', self.pin, 'lean', '--version'],
                                         cwd=self.root, env=self.env, text=True, timeout=10)
        with patch.object(worker_env.subprocess, 'check_output',
                          return_value='Lean (version 4.34.0, fixture)\n'):
            with self.assertRaisesRegex(ValueError, 'does not match'):
                worker_env.check_environment(self.root, self.env, lean_version=True)

    def test_command_preserves_literal_arguments_cwd_environment_and_status(self):
        missing_cache = self.root / 'not bootstrapped'
        env = {**os.environ, **self.inherited, 'TRUTH_CORE_VERIFIER_HOME': str(missing_cache)}
        arguments = ['--check', 'a b', '$HOME; $(false)', '`false`', "quote'\"", 'line\nbreak']
        code = ('import json,os,sys; print(json.dumps(dict(args=sys.argv[1:], '
                'cwd=os.getcwd(), cache=os.environ["TRUTH_CORE_VERIFIER_HOME"], '
                'path=os.environ["PATH"]))); sys.exit(23)')
        result = subprocess.run([sys.executable, str(Path(worker_env.__file__).resolve()),
                                 '--', sys.executable, '-c', code, *arguments],
                                cwd=self.root, env=env, text=True, capture_output=True)
        self.assertEqual(result.returncode, 23, result.stderr)
        report = json.loads(result.stdout)
        self.assertEqual(report['args'], arguments)
        self.assertEqual(report['cwd'], str(self.root))
        self.assertEqual(report['cache'], str(missing_cache))
        self.assertEqual(report['path'], str(self.root / 'home/.elan/bin') + ':/fixture/bin')
        self.assertFalse(missing_cache.exists())  # No preflight, bootstrap or downloads.


if __name__ == '__main__':
    unittest.main()
