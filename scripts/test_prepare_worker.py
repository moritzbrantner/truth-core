"""Offline fixtures exercise the public preparation boundaries without downloads."""

import importlib.util
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

SPEC = importlib.util.spec_from_file_location("prepare_worker", Path(__file__).with_name("prepare-worker.py"))
worker = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(worker)


class PreparationTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name) / "clone"
        self.root.mkdir()
        subprocess.run(["git", "init", "-q", str(self.root)], check=True)
        subprocess.run(["git", "-C", str(self.root), "remote", "add", "origin",
                        "https://github.com/moritzbrantner/truth-core.git"], check=True)
        for name in ("lean-toolchain", "lake-manifest.json", "bun.lock", "scripts/bootstrap-verifier.sh"):
            path = self.root / name
            path.parent.mkdir(exist_ok=True)
            path.touch()
        (self.root / "package.json").write_text(json.dumps({"workspaces": ["apps/*"]}))
        self.app = self.root / "apps/explorer"
        self.app.mkdir(parents=True)
        (self.app / "package.json").write_text("{}")

    def test_verifier_tag_fetch_is_retained_for_offline_warm_reuse(self):
        upstream = self.root.parent / "upstream"
        subprocess.run(["git", "init", "-q", str(upstream)], check=True)
        subprocess.run(["git", "-C", str(upstream), "-c", "user.name=Fixture",
                        "-c", "user.email=fixture@example.invalid", "commit", "--allow-empty", "-qm", "fixture"], check=True)
        subprocess.run(["git", "-C", str(upstream), "tag", "v0.0.1"], check=True)
        cache = self.root.parent / "verifier-cache"
        subprocess.run(["git", "clone", "--quiet", "--no-tags", str(upstream), str(cache)], check=True)
        script = Path(__file__).with_name("bootstrap-verifier.sh").read_text()
        function = script[script.index("clone_at() {"):script.index("# lean4export tags")]
        command = ["bash", "-c", "set -euo pipefail\n" + function + 'clone_at "$1" "$2" "$3"',
                   "fixture", str(upstream), "v0.0.1", str(cache)]
        subprocess.run(command, check=True, capture_output=True)
        self.assertEqual(subprocess.check_output(["git", "-C", str(cache), "rev-parse", "HEAD"], text=True),
                         subprocess.check_output(["git", "-C", str(cache), "rev-parse", "v0.0.1^{commit}"], text=True))
        upstream.rename(upstream.with_name("unavailable-upstream"))
        subprocess.run(command, check=True, capture_output=True)

    def test_explicit_clone_and_symlink_guards(self):
        self.assertEqual(worker.worker_clone(self.root), self.root)
        for invalid in (self.root.parent, Path.home(), Path("/")):
            with self.assertRaises(ValueError):
                worker.worker_clone(invalid)
        link = self.root.parent / "alias"
        link.symlink_to(self.root, target_is_directory=True)
        with self.assertRaises(ValueError):
            worker.worker_clone(link)
        (self.root / ".git").rename(self.root / "git-directory")
        (self.root / ".git").write_text("gitdir: ../git-directory")
        with self.assertRaises(ValueError):
            worker.worker_clone(self.root)

    def test_stale_layout_removed_and_warm_layout_preserved(self):
        installs = [self.root / "node_modules", self.app / "node_modules"]
        for path in installs:
            (path / ".bun").mkdir(parents=True)
            (path / "stale").touch()
        calls = []

        def bun(root, *command, capture=False, env=None):
            if command == ("bun", "--version"):
                return "1.4.3\n"
            self.assertEqual(env["NODE_ENV"], "development")
            calls.append(command)
            for path in installs:
                self.assertFalse((path / "stale").exists())
            installs[0].mkdir(exist_ok=True)
            (installs[0] / "installed").touch(exist_ok=True)

        original_run = worker.run
        with patch.object(worker, "run", side_effect=lambda root, *cmd, **kw:
                          bun(root, *cmd, **kw) if cmd[0] == "bun" else original_run(root, *cmd, **kw)):
            worker.prepare_bun(self.root)
            before = (installs[0] / "installed").stat().st_ino
            worker.prepare_bun(self.root)
            self.assertEqual(before, (installs[0] / "installed").stat().st_ino)
            self.assertEqual(len(calls), 1)
        self.assertEqual(calls, [("bun", "--config=/dev/null", "install", "--linker=hoisted", "--frozen-lockfile")])

    def test_receipt_invalidates_missing_changed_outputs_and_inputs(self):
        installed = self.root / "installed"
        calls = []

        def acquire():
            calls.append("acquire")
            installed.write_text("valid")

        output = lambda: worker.install_digest([self.root / "output"])
        # Use the same real file-tree boundary as the Bun receipt.
        directory = self.root / "output"
        directory.mkdir()
        installed = directory / "installed"
        worker.reconcile(self.root, "bun", "inputs", output, acquire)
        receipt = self.root / ".git/truth-core-preparation.json"
        before = receipt.stat().st_mtime_ns
        worker.reconcile(self.root, "bun", "inputs", output, acquire)
        self.assertEqual(len(calls), 1)
        self.assertEqual(receipt.stat().st_mtime_ns, before)
        installed.unlink()
        worker.reconcile(self.root, "bun", "inputs", output, acquire)
        installed.write_text("changed output")
        worker.reconcile(self.root, "bun", "inputs", output, acquire)
        worker.reconcile(self.root, "bun", "new inputs", output, acquire)
        self.assertEqual(len(calls), 4)

    def test_all_cleanup_targets_checked_before_deletion(self):
        modules = self.root / "node_modules"
        (modules / ".bun").mkdir(parents=True)
        outside = self.root.parent / "outside"
        outside.mkdir()
        sentinel = outside / "keep"
        sentinel.touch()
        (self.app / "node_modules").symlink_to(outside, target_is_directory=True)
        with self.assertRaises(ValueError):
            worker.prepare_bun(self.root)
        self.assertTrue((modules / ".bun").exists())
        self.assertTrue(sentinel.exists())

    def test_tracked_install_content_refused(self):
        path = self.root / "node_modules/keep"
        path.parent.mkdir()
        path.touch()
        subprocess.run(["git", "-C", str(self.root), "add", "node_modules/keep"], check=True)
        with self.assertRaises(ValueError):
            worker.prepare_bun(self.root)
        self.assertTrue(path.exists())

    def test_absent_post_install_output_never_records_readiness(self):
        with self.assertRaisesRegex(ValueError, "did not produce required artifacts"):
            worker.reconcile(self.root, "verifier", "inputs", lambda: None, lambda: None)
        self.assertFalse((self.root / ".git/truth-core-preparation.json").exists())

    def test_dirty_or_wrong_revision_dependency_refused(self):
        package = self.root / ".lake/packages/mathlib"
        package.mkdir(parents=True)
        (self.root / "lake-manifest.json").write_text(json.dumps({
            "packagesDir": ".lake/packages", "packages": [{"name": "mathlib", "type": "git", "rev": "pinned"}]}))
        with patch.object(worker, "run", return_value="other\n"):
            with self.assertRaisesRegex(ValueError, "revision mismatch"):
                worker.check_packages(self.root)
        with patch.object(worker, "run", side_effect=["old pin\n", ""]):
            worker.check_packages(self.root, acquiring=True)
        with patch.object(worker, "run", side_effect=["pinned\n", " M lakefile.lean\n"]):
            with self.assertRaisesRegex(ValueError, "modified pinned"):
                worker.check_packages(self.root)


if __name__ == "__main__":
    unittest.main()
