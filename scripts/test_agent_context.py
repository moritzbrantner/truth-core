"""Exercise configured hook commands without assuming runtime hook activation."""

import json
from pathlib import Path
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]


class AgentContextTest(unittest.TestCase):
    def test_configured_events_work_from_nested_directory_without_git_mutation(self):
        hooks = json.loads((ROOT / ".codex/hooks.json").read_text())["hooks"]
        before = subprocess.check_output(["git", "status", "--porcelain"], cwd=ROOT)
        for event, groups in hooks.items():
            with self.subTest(event=event):
                handler = groups[0]["hooks"][0]
                run = subprocess.run(handler["command"], shell=True, cwd=ROOT / "scripts",
                                     input=json.dumps({"hook_event_name": event, "cwd": str(ROOT / "scripts")}),
                                     capture_output=True, text=True, timeout=3)
                self.assertEqual(run.returncode, 0, run.stderr)
                out = json.loads(run.stdout)["hookSpecificOutput"]
                self.assertEqual(out["hookEventName"], event)
                self.assertIn(str(ROOT), out["additionalContext"])
                self.assertIn(".agents/skills/truth-core-research/SKILL.md", out["additionalContext"])
                self.assertLess(len(out["additionalContext"]), 3000)
        self.assertEqual(before, subprocess.check_output(["git", "status", "--porcelain"], cwd=ROOT))

    def test_nonrepository_and_bad_input_fail_soft(self):
        with tempfile.TemporaryDirectory() as directory:
            for event in ({"hook_event_name": "SessionStart", "cwd": directory}, []):
                run = subprocess.run(["python3", "-B", str(ROOT / "scripts/agent_context.py"), "--hook"],
                                     input=json.dumps(event), text=True, capture_output=True)
                self.assertEqual(run.returncode, 0)
                self.assertFalse(run.stdout)

    def test_other_event_is_noop(self):
        run = subprocess.run(["python3", "-B", str(ROOT / "scripts/agent_context.py"), "--hook"],
                             input='{"hook_event_name":"Stop"}', text=True, capture_output=True)
        self.assertEqual(run.returncode, 0)
        self.assertFalse(run.stdout)


if __name__ == "__main__":
    unittest.main()
