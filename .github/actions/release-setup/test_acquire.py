import importlib.util
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import urllib.error

spec = importlib.util.spec_from_file_location('acquire', Path(__file__).with_name('acquire.py'))
a = importlib.util.module_from_spec(spec)
spec.loader.exec_module(a)


class AcquisitionTest(unittest.TestCase):
    def test_auth_redirect_and_retry(self):
        calls = []
        def request(req, timeout):
            calls.append(req)
            self.assertEqual(timeout, 60)
            if len(calls) == 1:
                raise urllib.error.HTTPError(req.full_url, 504, 'timeout', {}, None)
            if req.host == 'api.github.com':
                raise urllib.error.HTTPError(req.full_url, 302, 'redirect',
                                             {'Location': 'https://release-assets.githubusercontent.com/file?secret=signed'}, None)
            return io.BytesIO(b'official binary')
        with tempfile.TemporaryDirectory() as tmp, patch.dict('os.environ', GH_TOKEN='fixture-token'), patch.object(a.OPENER, 'open', side_effect=request), patch.object(a.time, 'sleep') as sleep:
            target = Path(tmp) / 'asset'
            a.fetch('https://api.github.com/repos/leanprover/lean4/releases/assets/123', target, True)
            self.assertEqual(target.read_bytes(), b'official binary')
            self.assertEqual([r.get_header('Authorization') for r in calls],
                             ['Bearer fixture-token', 'Bearer fixture-token', None])
            self.assertTrue(all(r.get_header('Accept') == 'application/octet-stream' for r in calls))
            sleep.assert_called_once_with(2)

    def test_direct_binary_response(self):
        with tempfile.TemporaryDirectory() as tmp, patch.dict('os.environ', GH_TOKEN='token'), patch.object(a.OPENER, 'open', return_value=io.BytesIO(b'binary')):
            target = Path(tmp) / 'asset'
            a.fetch('https://api.github.com/repos/leanprover/elan/releases/assets/1', target, True)
            self.assertEqual(target.read_bytes(), b'binary')

    def test_fatal_statuses_never_retry(self):
        for code in [401, 403, 404]:
            with self.subTest(code=code), tempfile.TemporaryDirectory() as tmp, patch.dict('os.environ', GH_TOKEN='token'), patch.object(a.OPENER, 'open', side_effect=urllib.error.HTTPError('hidden', code, 'error', {}, None)) as op, patch.object(a.time, 'sleep') as sleep:
                with self.assertRaisesRegex(RuntimeError, str(code)):
                    a.fetch('https://api.github.com/repos/a/b/releases/assets/1', Path(tmp)/'file', True)
                self.assertEqual(op.call_count, 1)
                sleep.assert_not_called()

    def test_retries_bounded(self):
        with tempfile.TemporaryDirectory() as tmp, patch.dict('os.environ', GH_TOKEN='token'), patch.object(a.OPENER, 'open', side_effect=urllib.error.HTTPError('hidden', 504, 'error', {}, None)) as op, patch.object(a.time, 'sleep') as sleep:
            with self.assertRaises(RuntimeError):
                a.fetch('https://api.github.com/repos/a/b/releases/assets/1', Path(tmp)/'file', True)
            self.assertEqual(op.call_count, 4)
            self.assertEqual([c.args[0] for c in sleep.call_args_list], [2, 4, 8])

    def test_untrusted_redirect_rejected_before_request(self):
        for url in ['https://evil.example/file', 'http://release-assets.githubusercontent.com/file', 'https://api.github.com@evil.example/file']:
            with self.subTest(url=url), tempfile.TemporaryDirectory() as tmp, patch.dict('os.environ', GH_TOKEN='token'), patch.object(a.OPENER, 'open', side_effect=urllib.error.HTTPError('hidden', 302, 'redirect', {'Location': url}, None)) as op:
                with self.assertRaises(ValueError):
                    a.fetch('https://api.github.com/repos/a/b/releases/assets/1', Path(tmp)/'file', True)
                self.assertEqual(op.call_count, 1)

    def test_version_and_architecture_selection(self):
        def metadata(repo, tag):
            names = {'leanprover/lean4': ['lean-4.35.0-linux.tar.zst', 'lean-4.35.0-linux_aarch64.tar.zst'],
                     'leanprover/elan': ['elan-x86_64-unknown-linux-gnu.tar.gz', 'elan-aarch64-unknown-linux-gnu.tar.gz'],
                     'oven-sh/bun': ['bun-linux-x64-baseline.zip', 'bun-linux-aarch64.zip']}[repo]
            return {'tag_name': 'bun-v9.8.7' if repo == 'oven-sh/bun' else 'v4.35.0',
                    'assets': [{'id': i+1, 'name': name, 'size': 10, 'state': 'uploaded'} for i, name in enumerate(names)]}
        for arch in ['x86_64', 'aarch64']:
            with patch.object(a.platform, 'system', return_value='Linux'), patch.object(a.platform, 'machine', return_value=arch), patch.object(a, 'release', side_effect=metadata) as release, patch.object(Path, 'read_text', return_value='leanprover/lean4:v4.35.0\n'):
                lean = a.plan('lean')
                self.assertEqual(lean['pin'], 'leanprover/lean4:v4.35.0')
                self.assertEqual(lean['assets'][1]['id'], 1 if arch == 'x86_64' else 2)
                release.assert_any_call('leanprover/lean4', 'v4.35.0')
                bun = a.plan('bun')
                self.assertEqual(bun['version'], 'bun-v9.8.7')
                release.assert_any_call('oven-sh/bun', 'latest')

    def test_cold_lean_install_uses_both_rest_asset_ids(self):
        config = {'pin': 'leanprover/lean4:v4.35.0', 'assets': [
            {'repo': 'leanprover/elan', 'id': 11, 'name': 'elan.tar.gz'},
            {'repo': 'leanprover/lean4', 'id': 22, 'name': 'lean.tar.zst'}]}
        with tempfile.TemporaryDirectory() as tmp, patch.object(a, 'fetch') as fetch, patch.object(a.subprocess, 'run') as run:
            root = Path(tmp)
            a.install(config, root)
            self.assertEqual([call.args[0] for call in fetch.call_args_list], [
                'https://api.github.com/repos/leanprover/elan/releases/assets/11',
                'https://api.github.com/repos/leanprover/lean4/releases/assets/22'])
            self.assertTrue(all(call.args[2] is True for call in fetch.call_args_list))
            self.assertTrue((root/'elan/toolchains/leanprover--lean4---v4.35.0').is_dir())
            self.assertIn('--default-toolchain', run.call_args_list[1].args[0])
            self.assertIn('none', run.call_args_list[1].args[0])

    def test_cached_validation_uses_no_network_and_checks_versions(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            binary = root / '.cache/truth-core-release/bun/bin/bun'
            binary.parent.mkdir(parents=True)
            binary.write_text('#!/bin/sh\necho 9.8.7\n')
            binary.chmod(0o755)
            (root/'bun-release.json').write_text(json.dumps({'version': 'bun-v9.8.7'}))
            env = {'RUNNER_TEMP': tmp, 'GITHUB_PATH': str(root/'path')}
            with patch.object(Path, 'home', return_value=root), patch.dict('os.environ', env), patch('sys.argv', ['acquire', 'validate', 'bun']), patch.object(a, 'fetch', side_effect=AssertionError('cached validation used network')):
                a.main()
                self.assertIn(str(binary.parent), (root/'path').read_text())
                binary.write_text('#!/bin/sh\necho 1.0.0\n')
                with self.assertRaisesRegex(ValueError, 'differs'):
                    a.main()

    def test_malformed_assets(self):
        for assets in [[], [{'name': 'binary', 'id': 'wrong'}], [{'name': 'binary'}]*2]:
            with self.assertRaises(ValueError):
                a.asset({'assets': assets}, 'binary')

    def test_consumers_avoid_original_anonymous_paths(self):
        github = Path(__file__).resolve().parents[2]
        for path in [*github.glob('actions/*/action.yml'), *github.glob('workflows/*.yml')]:
            text = path.read_text()
            self.assertNotIn('uses: leanprover/lean-action@', text)
            self.assertNotIn('uses: oven-sh/setup-bun@', text)
        text = (github/'actions/release-setup/action.yml').read_text()
        self.assertLess(text.index('actions/cache/restore@'), text.index('install "$TOOL"'))
        self.assertIn("steps.cache.outputs.cache-hit != 'true'", text)
        self.assertIn("github.ref == 'refs/heads/main'", text)
        self.assertIn("github.event_name != 'pull_request'", text)
        self.assertIn('runner.os', text)
        self.assertIn('runner.arch', text)
        self.assertIn('steps.release.outputs.version', text)
        self.assertIn('lake exe cache get', (github/'actions/lean-setup/action.yml').read_text())


if __name__ == '__main__':
    unittest.main()
