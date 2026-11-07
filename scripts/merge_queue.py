#!/usr/bin/env python3
"""Local merge queue for parallel worker PRs (owner direction, 2026-11-07).

    python3 scripts/merge_queue.py --workdir CLONE PR [PR ...] [--poll SECONDS] [--once]

Processes the PRs in the given order until each is merged or blocked:

* CLEAN with no failing check: merge (`--merge`), deleting the head branch only
  when no other open PR uses it as its base (a deleted base closes stacked PRs).
* Behind or conflicting with main: in CLONE (a standalone truth-core clone that
  no one else writes to), check out the PR branch, merge origin/main, and
  resolve conflicts ONLY in generated files by regenerating them
  (`scripts/root-imports.sh --write`, `python3 scripts/docs_index.py --write`).
  Then run `python3 scripts/corpus.py check` and push, which restarts CI. A
  conflict in any other file aborts the merge and reports the PR as blocked: it
  needs a human or the authoring worker.
* A failing check: report and leave the PR alone.
* A PR whose base is not main: report it (stacked PRs must be retargeted first).

It never force-pushes, never edits a PR's content beyond regenerated files, and
never merges a PR with a failing or missing required check. One queue runs at a
time; it holds no lock on CI and relies on GitHub's own checks.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
import time
from pathlib import Path

GENERATED_PREFIXES = ("TruthCore/Imports/",)
GENERATED_FILES = ("TruthCore.lean",)


def run(cmd: list[str], cwd: Path | None = None, check: bool = True) -> subprocess.CompletedProcess:
    return subprocess.run(cmd, cwd=cwd, check=check, capture_output=True, text=True)


def gh_json(args: list[str]) -> dict | list:
    return json.loads(run(["gh", *args]).stdout)


def pr_state(number: int) -> dict:
    return gh_json(["pr", "view", str(number), "--json",
                    "state,mergeStateStatus,mergeable,baseRefName,headRefName,isDraft"])


def check_summary(number: int) -> tuple[int, int, int]:
    """(passed, pending, failed) over the PR's checks."""
    out = run(["gh", "pr", "checks", str(number)], check=False).stdout
    passed = pending = failed = 0
    for line in out.splitlines():
        parts = line.split("\t")
        if len(parts) < 2:
            continue
        status = parts[1]
        if status == "pass":
            passed += 1
        elif status in ("pending", "queued", "in_progress"):
            pending += 1
        elif status == "fail":
            failed += 1
    return passed, pending, failed


def is_generated(path: str) -> bool:
    return path.startswith(GENERATED_PREFIXES) or path in GENERATED_FILES


def refresh(number: int, head: str, workdir: Path) -> str:
    """Merge origin/main into the PR branch, regenerating generated files.
    Returns 'pushed', 'up-to-date' or 'blocked: <reason>'."""
    run(["git", "fetch", "-q", "origin"], cwd=workdir)
    status = run(["git", "status", "--porcelain", "--untracked-files=no"], cwd=workdir).stdout
    if status.strip():
        return "blocked: workdir has uncommitted tracked changes"
    run(["git", "checkout", "-q", "-B", head, f"origin/{head}"], cwd=workdir)
    merge = run(["git", "merge", "--no-edit", "origin/main"], cwd=workdir, check=False)
    if merge.returncode != 0:
        conflicted = run(["git", "diff", "--name-only", "--diff-filter=U"], cwd=workdir).stdout.split()
        others = [path for path in conflicted if not is_generated(path)]
        if others:
            run(["git", "merge", "--abort"], cwd=workdir, check=False)
            return f"blocked: conflicts outside generated files: {', '.join(others)}"
        for path in conflicted:
            run(["git", "checkout", "--theirs", "--", path], cwd=workdir)
    run(["scripts/root-imports.sh", "--write"], cwd=workdir)
    run([sys.executable, "scripts/docs_index.py", "--write"], cwd=workdir)
    run(["git", "add", "-A", "--", "TruthCore/Imports", "TruthCore.lean", "docs"], cwd=workdir)
    if merge.returncode != 0 or run(["git", "diff", "--cached", "--quiet"], cwd=workdir, check=False).returncode:
        run(["git", "commit", "-q", "--no-edit"] if merge.returncode != 0 else
            ["git", "commit", "-q", "-m", "Regenerate generated files"], cwd=workdir)
    check = run([sys.executable, "scripts/corpus.py", "check"], cwd=workdir, check=False)
    if check.returncode != 0:
        tail = (check.stdout + check.stderr).strip().splitlines()[-1:]
        return f"blocked: corpus check fails after merging main: {' '.join(tail)}"
    ahead = run(["git", "rev-list", "--count", f"origin/{head}..HEAD"], cwd=workdir).stdout.strip()
    if ahead == "0":
        return "up-to-date"
    push = run(["git", "push", "-q", "origin", f"HEAD:{head}"], cwd=workdir, check=False)
    if push.returncode != 0:
        return f"blocked: push failed: {push.stderr.strip()}"
    return "pushed"


def merge(number: int, head: str) -> str:
    bases = {pr["baseRefName"] for pr in gh_json(["pr", "list", "--state", "open", "--json", "baseRefName,number"])
             if pr["number"] != number}
    args = ["gh", "pr", "merge", str(number), "--merge"]
    if head not in bases:
        args.append("--delete-branch")
    result = run(args, check=False)
    return "merged" if result.returncode == 0 else f"merge failed: {result.stderr.strip()}"


def step(number: int, workdir: Path, refreshed: set[int]) -> str:
    """One pass over a PR; returns a terminal outcome or 'waiting'."""
    state = pr_state(number)
    if state["state"] != "OPEN":
        return state["state"].lower()
    if state["baseRefName"] != "main":
        return f"blocked: base is {state['baseRefName']}, retarget to main first"
    if state["isDraft"]:
        return "blocked: draft"
    passed, pending, failed = check_summary(number)
    if failed:
        return f"blocked: {failed} failing check(s)"
    merge_state = state["mergeStateStatus"]
    if merge_state in ("DIRTY", "BEHIND") or state["mergeable"] == "CONFLICTING":
        outcome = refresh(number, state["headRefName"], workdir)
        if outcome.startswith("blocked"):
            return outcome
        refreshed.add(number)
        return "waiting"
    if merge_state == "CLEAN" and not pending and passed:
        return merge(number, state["headRefName"])
    return "waiting"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("prs", nargs="+", type=int)
    parser.add_argument("--workdir", required=True, type=Path,
                        help="standalone clone used only for resolving generated-file conflicts")
    parser.add_argument("--poll", type=int, default=60)
    parser.add_argument("--once", action="store_true", help="one pass over every PR, then exit")
    args = parser.parse_args()
    pending = list(args.prs)
    refreshed: set[int] = set()
    results: dict[int, str] = {}
    while pending:
        for number in list(pending):
            outcome = step(number, args.workdir.resolve(), refreshed)
            if outcome != "waiting":
                results[number] = outcome
                pending.remove(number)
                print(f"{number}: {outcome}", flush=True)
        if args.once or not pending:
            break
        time.sleep(args.poll)
    for number in pending:
        print(f"{number}: waiting", flush=True)
    return 0 if not pending and all(r == "merged" for r in results.values()) else 1


if __name__ == "__main__":
    raise SystemExit(main())
