#!/usr/bin/env python3
"""Emit compact, read-only research context for native Codex startup hooks."""

import argparse
import json
import os
from pathlib import Path
import subprocess
import sys

from agent_lean import settings


def context(cwd: Path) -> str:
    top = subprocess.check_output(
        ["git", "-C", str(cwd), "rev-parse", "--show-toplevel"], text=True,
        stderr=subprocess.DEVNULL, timeout=2).strip()
    root = Path(top)
    if not all((root / path).is_file() for path in ("TruthCore.lean", "AGENTS.md", "scripts/corpus.py")):
        return ""
    head = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True, timeout=2).strip()
    service = settings(root, dict(os.environ))
    supplied = ", ".join(f"{key}={value}" for key, value in service.items() if value)
    return (
        f"Truth Core checkout: {root}; HEAD {head}.\n"
        "For repository research use .agents/skills/truth-core-research/SKILL.md and the supplied "
        "four-line brief. AGENTS.md remains the policy authority; docs/agent-service.md describes "
        "the shared preview protocol.\n"
        f"Local service settings: {supplied or 'not configured; use the coordinator-supplied explicit flags'}. "
        "These are configuration values, not health or verification evidence.\n"
        "scripts/agent_lean.py submits full edits with the shared lease and binding checks. "
        "Use worker_env.py command mode with the supplied setup; do not repeat its preflight. "
        "Reuse unchanged check evidence and keep required final CI. This startup hook performs "
        "no preparation, service call, source/proof check, or repository write."
    )


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--hook", action="store_true", help="read the native hook JSON event on stdin")
    args = parser.parse_args(argv)
    try:
        event = json.load(sys.stdin) if args.hook else {}
        if not isinstance(event, dict):
            raise ValueError("hook event must be an object")
        name = event.get("hook_event_name", "SessionStart")
        if name not in ("SessionStart", "SubagentStart"):
            return 0
        message = context(Path(event.get("cwd") or os.getcwd()))
        if message:
            print(json.dumps({"hookSpecificOutput": {"hookEventName": name, "additionalContext": message}}))
        return 0
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        # Advisory startup context must not prevent research when Git/context is unavailable.
        print(f"agent_context: {error}", file=sys.stderr)
        return 0


if __name__ == "__main__":
    raise SystemExit(main())
