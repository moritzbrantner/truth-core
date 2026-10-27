"""Non-Lean endpoints of the local agent service (#489)."""

import json
import subprocess
import sys
import tempfile
import threading
import time
import unittest
import urllib.error
import urllib.request
from pathlib import Path
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent))

import agent_service  # noqa: E402

STATEMENT = {"id": "STMT-FIXTURE", "paraphrase": "A fixture statement.", "lean_declaration": "X"}


def make_workspace(root: Path) -> None:
    """A git checkout whose corpus.py echoes its arguments as JSON."""
    (root / "scripts").mkdir()
    (root / "scripts" / "corpus.py").write_text(
        "import json, sys\nprint(json.dumps({'argv': sys.argv[1:]}))\n", encoding="utf-8"
    )
    (root / "corpus" / "statements").mkdir(parents=True)
    (root / "corpus" / "statements" / "fixture.json").write_text(json.dumps(STATEMENT), encoding="utf-8")
    for args in (["init", "-q"], ["add", "."], ["-c", "user.name=t", "-c", "user.email=t@t", "commit", "-qm", "x"]):
        subprocess.run(["git", *args], cwd=root, check=True)


class AgentServiceTest(unittest.TestCase):
    def setUp(self) -> None:
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.workspace = Path(tmp.name).resolve()
        make_workspace(self.workspace)
        self.server, self.service = agent_service.serve(0, self.workspace, ["false"], log=False)
        threading.Thread(target=self.server.serve_forever, daemon=True).start()
        self.addCleanup(self.server.server_close)
        self.addCleanup(self.server.shutdown)
        self.base = f"http://127.0.0.1:{self.server.server_address[1]}"

    def call(self, path: str, body: dict | None = None) -> tuple[int, dict]:
        data = json.dumps(body).encode() if body is not None else None
        try:
            with urllib.request.urlopen(urllib.request.Request(self.base + path, data=data)) as response:
                return response.status, json.load(response)
        except urllib.error.HTTPError as error:
            with error:
                return error.code, json.load(error)

    def test_health_binds_revision(self) -> None:
        head = subprocess.run(["git", "rev-parse", "HEAD"], cwd=self.workspace, capture_output=True, text=True).stdout
        status, body = self.call("/health")
        self.assertEqual(status, 200)
        self.assertEqual(self.server.server_address[0], "127.0.0.1")
        self.assertEqual(body["result"]["status"], "ok")
        self.assertEqual(body["binding"]["head"], head.strip())
        self.assertFalse(body["binding"]["dirty"])
        (self.workspace / "untracked.txt").write_text("x", encoding="utf-8")
        _, body = self.call("/health")
        self.assertTrue(body["binding"]["dirty"])
        self.assertIn("diff_sha256", body["binding"])

    def test_record_lookup(self) -> None:
        status, body = self.call("/corpus/record?id=STMT-FIXTURE")
        self.assertEqual(status, 200)
        self.assertEqual(body["result"]["record"], STATEMENT)
        self.assertEqual(body["result"]["path"], "corpus/statements/fixture.json")
        self.assertEqual(body["binding"]["inputs"]["file_sha256"], body["result"]["file_sha256"])
        self.assertEqual(self.call("/corpus/record?id=STMT-MISSING")[0], 404)
        self.assertEqual(self.call("/corpus/record?id=../x")[0], 400)

    def test_corpus_commands_wrap_cli(self) -> None:
        _, body = self.call("/corpus/dossier?id=STMT-FIXTURE")
        self.assertEqual(body["result"]["data"]["argv"], ["dossier", "--json", "STMT-FIXTURE"])
        _, body = self.call("/corpus/frontier?reaching_root=1")
        self.assertEqual(body["result"]["data"]["argv"], ["frontier", "--json", "--reaching-root"])
        _, body = self.call("/corpus/check", {})
        self.assertEqual(body["result"]["returncode"], 0)

    def test_rejects_paths_and_workspaces_outside(self) -> None:
        status, body = self.call("/lean/diagnostics", {"path": "../outside.lean"})
        self.assertEqual(status, 400)
        status, _ = self.call("/health?workspace=/")
        self.assertEqual(status, 400)
        self.assertEqual(self.call("/nowhere")[0], 404)

    def test_jobs_run_one_at_a_time(self) -> None:
        script = "import time; time.sleep(0.2); print('done')"
        with mock.patch.object(agent_service, "job_command", lambda kind, body: [sys.executable, "-c", script]):
            ids = [self.call("/jobs", {"kind": "build"})[1]["result"]["id"] for _ in range(2)]
            deadline = time.time() + 10
            while time.time() < deadline:
                jobs = [self.call(f"/jobs/{job_id}")[1]["result"] for job_id in ids]
                if all(job["status"] == "passed" for job in jobs):
                    break
                time.sleep(0.05)
        self.assertEqual([job["status"] for job in jobs], ["passed", "passed"])
        self.assertIn("done", jobs[0]["output"])
        self.assertLessEqual(jobs[0]["finished"], jobs[1]["started"])
        self.assertFalse(jobs[0]["inputs_changed_during_job"])
        self.assertEqual(self.call("/jobs", {"kind": "unknown"})[0], 400)
        self.assertEqual(self.call("/jobs", {"kind": "verify-result", "result_id": "a;b"})[0], 400)


if __name__ == "__main__":
    unittest.main()
