"""Client-side protocol/lease tests; no Lean process or proof verification."""

import contextlib
import fcntl
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
import io
import json
from pathlib import Path
import subprocess
import tempfile
import threading
import unittest

import agent_lean


class AgentLeanTest(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        self.workspace = self.root / "preview"
        (self.workspace / "scripts").mkdir(parents=True)
        (self.workspace / "scripts/corpus.py").write_text("# fixture\n")
        self.input = self.root / "canonical.lean"
        self.input.write_text("example : True := True.intro\n")
        self.lock = self.root / "shared.lock"
        for args in (["init", "-q"], ["add", "."], ["-c", "user.name=t", "-c", "user.email=t@t", "commit", "-qm", "fixture"]):
            subprocess.run(["git", *args], cwd=self.workspace, check=True)
        self.requests = []
        self.entered = threading.Event()
        self.alter = lambda response: None
        self.http_status = 200
        self.lease_held = False
        test = self

        class Handler(BaseHTTPRequestHandler):
            def do_POST(self):
                payload = json.loads(self.rfile.read(int(self.headers["Content-Length"])))
                test.requests.append((self.path, payload))
                test.entered.set()
                with test.lock.open("a") as probe:
                    try:
                        fcntl.flock(probe, fcntl.LOCK_EX | fcntl.LOCK_NB)
                    except BlockingIOError:
                        test.lease_held = True
                binding = agent_lean.revision(test.workspace)
                binding["inputs"] = {key: payload[key] for key in ("session", "path")}
                binding["inputs"].update(content_source="request", content_sha256=agent_lean.sha256(payload["content"]))
                for key in ("line", "character"):
                    if key in payload:
                        binding["inputs"][key] = payload[key]
                result = {"uri": (test.workspace / payload["path"]).as_uri(), "version": 1,
                          "diagnostics": [], "elapsed_s": 0.001}
                if self.path.endswith("goal"):
                    result["goal"] = {"plainGoal": "fixture"}
                response = {"binding": binding, "result": result}
                test.alter(response)
                self.send_response(test.http_status)
                self.end_headers()
                self.wfile.write(json.dumps(response).encode())

            def log_message(self, *args):
                pass

        self.server = ThreadingHTTPServer(("127.0.0.1", 0), Handler)
        self.addCleanup(self.server.server_close)
        self.addCleanup(self.server.shutdown)
        threading.Thread(target=self.server.serve_forever, daemon=True).start()
        self.url = f"http://127.0.0.1:{self.server.server_address[1]}"

    def submit(self, **kwargs):
        return agent_lean.submit(self.url, self.workspace, "shared", "Scratch/task.lean",
                                 self.input.read_text(), self.lock, 2, **kwargs)

    def test_full_edit_dirty_preview_and_held_lease(self):
        (self.workspace / "Scratch").mkdir()
        (self.workspace / "Scratch/unrelated.lean").write_text("-- preexisting scratch\n")
        response = self.submit()
        self.assertTrue(response["binding"]["dirty"])
        self.assertEqual(self.requests[0][1]["content"], self.input.read_text())
        self.assertEqual(self.requests[0][1]["workspace"], str(self.workspace))
        self.assertTrue(self.lease_held)
        with self.lock.open("a") as probe:
            fcntl.flock(probe, fcntl.LOCK_EX | fcntl.LOCK_NB)
        self.assertEqual(response["result"]["elapsed_s"], 0.001)
        self.assertGreaterEqual(response["client"]["total_s"], response["client"]["request_s"])

    def test_foreign_workspace_or_revision_rejected(self):
        for field, value in (("workspace", str(self.root)), ("head", "0" * 40), ("dirty", True)):
            with self.subTest(field=field):
                self.alter = lambda response: response["binding"].update({field: value})
                with self.assertRaisesRegex(ValueError, "revision/workspace"):
                    self.submit()

    def test_foreign_session_content_path_position_rejected(self):
        for field, value in (("session", "another"), ("content_sha256", "0" * 64),
                             ("path", "Scratch/other.lean"), ("content_source", "disk"), ("line", 2)):
            with self.subTest(field=field):
                self.alter = lambda response: response["binding"]["inputs"].update({field: value})
                with self.assertRaisesRegex(ValueError, "input binding"):
                    self.submit(position=(0, 0))

    def test_malformed_result_rejected(self):
        for field, value in (("uri", "file:///foreign.lean"), ("version", True),
                             ("diagnostics", [{} , {"severity": "1"}])):
            with self.subTest(field=field):
                self.alter = lambda response: response["result"].update({field: value})
                with self.assertRaisesRegex(ValueError, "malformed or foreign"):
                    self.submit()

    def test_changed_preview_rejected(self):
        self.alter = lambda response: (self.workspace / "scripts/corpus.py").write_text("# modified\n")
        with self.assertRaisesRegex(ValueError, "changed during"):
            self.submit()

    def test_stale_expected_head_rejected_before_post(self):
        with self.assertRaisesRegex(ValueError, "--expect-head"):
            self.submit(expect_head="0" * 40)
        self.assertFalse(self.requests)

    def test_paths_and_nonlocal_endpoint_rejected(self):
        for path in ("../outside.lean", "Scratch/not-lean.txt", str(self.workspace / "absolute.lean")):
            with self.subTest(path=path), self.assertRaises((ValueError, agent_lean.RequestError)):
                agent_lean.submit(self.url, self.workspace, "shared", path, "", self.lock, 2)
        with self.assertRaises(ValueError):
            agent_lean.local_url("http://127.0.0.1.example.org:8765")
        self.assertFalse(self.requests)

    def test_goal_uses_same_bound_full_edit(self):
        response = self.submit(position=(0, 0))
        self.assertEqual(self.requests[0][0], "/lean/goal")
        self.assertIn("goal", response["result"])

    def test_http_error_not_accepted_as_result(self):
        self.http_status = 400
        with self.assertRaisesRegex(ValueError, "service HTTP 400"):
            self.submit()

    def test_cli_error_diagnostics_exit_one_and_protocol_failure_two(self):
        arguments = [str(self.input), "--workspace", str(self.workspace), "--session", "shared",
                     "--path", "Scratch/task.lean", "--url", self.url, "--lock", str(self.lock)]
        self.alter = lambda response: response["result"].update(diagnostics=[{"severity": 1, "message": "bad proof"}])
        with contextlib.redirect_stdout(io.StringIO()) as output:
            self.assertEqual(agent_lean.main(arguments), 1)
        self.assertIn("binding", json.loads(output.getvalue()))
        self.alter = lambda response: response["binding"].update(workspace="/foreign")
        with contextlib.redirect_stderr(io.StringIO()):
            self.assertEqual(agent_lean.main(arguments), 2)

    def test_explicit_environment_overrides_local_config(self):
        subprocess.run(["git", "config", "--local", "truthcore.agentSession", "configured"], cwd=self.workspace, check=True)
        self.assertEqual(agent_lean.settings(self.workspace, {})["session"], "configured")
        self.assertEqual(agent_lean.settings(self.workspace, {"TRUTH_CORE_AGENT_SESSION": "env"})["session"], "env")

    def test_waiting_does_not_issue_request_before_lease(self):
        results = []
        with self.lock.open("a") as lease:
            fcntl.flock(lease, fcntl.LOCK_EX)
            thread = threading.Thread(target=lambda: results.append(self.submit()))
            thread.start()
            self.assertFalse(self.entered.wait(0.05))
        thread.join(timeout=5)
        self.assertFalse(thread.is_alive())
        self.assertGreaterEqual(results[0]["client"]["lease_wait_s"], 0.04)


if __name__ == "__main__":
    unittest.main()
