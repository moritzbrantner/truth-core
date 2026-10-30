#!/usr/bin/env python3
"""Submit a full Lean edit under the shared lease and validate its evidence binding."""

from __future__ import annotations

import argparse
import fcntl
import json
import math
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import time
import urllib.error
import urllib.parse
import urllib.request

from agent_service import file_in, revision, sha256, check_id, RequestError

SETTINGS = {
    "url": ("TRUTH_CORE_AGENT_URL", "truthcore.agentUrl"),
    "workspace": ("TRUTH_CORE_AGENT_WORKSPACE", "truthcore.agentWorkspace"),
    "session": ("TRUTH_CORE_AGENT_SESSION", "truthcore.agentSession"),
    "lock": ("TRUTH_CORE_AGENT_LOCK", "truthcore.agentLock"),
}


def settings(root: Path, env: dict[str, str]) -> dict[str, str]:
    """Read only local, non-secret service settings; never prepare an environment."""
    result = subprocess.run(
        ["git", "config", "--local", "--get-regexp", r"^truthcore\.agent"],
        cwd=root, text=True, capture_output=True, timeout=2,
    )
    if result.returncode not in (0, 1):
        raise ValueError(result.stderr.strip() or "cannot read local service settings")
    values = dict(line.split(None, 1) for line in result.stdout.splitlines() if len(line.split(None, 1)) == 2)
    return {name: env.get(variable) or values.get(key.lower(), "")
            for name, (variable, key) in SETTINGS.items()}


def local_url(value: str) -> str:
    parsed = urllib.parse.urlsplit(value)
    if (parsed.scheme != "http" or parsed.hostname != "127.0.0.1"
            or parsed.username or parsed.password or parsed.path not in ("", "/")
            or parsed.query or parsed.fragment):
        raise ValueError("service URL must be http://127.0.0.1:<port> without a path")
    _ = parsed.port  # reject malformed port syntax
    return value.rstrip("/")


def validate_response(response: dict, before: dict, after: dict, payload: dict) -> None:
    if before != after:
        raise ValueError("preview revision changed during diagnostics; response is not accepted")
    binding = response.get("binding")
    if not isinstance(binding, dict):
        raise ValueError("service response has no revision binding")
    actual = {key: value for key, value in binding.items() if key != "inputs"}
    if actual != before:
        raise ValueError("service revision/workspace binding differs from the leased preview")
    expected = {"session": payload["session"], "path": payload["path"],
                "content_source": "request", "content_sha256": sha256(payload["content"])}
    for key in ("line", "character"):
        if key in payload:
            expected[key] = payload[key]
    if binding.get("inputs") != expected:
        raise ValueError("service input binding differs from the submitted edit/session/position")
    result = response.get("result")
    path = file_in(Path(payload["workspace"]), payload["path"])
    if (not isinstance(result, dict) or result.get("uri") != path.as_uri()
            or type(result.get("version")) is not int or result["version"] < 1
            or not isinstance(result.get("diagnostics"), list)
            or any(not isinstance(diagnostic, dict)
                   or ("severity" in diagnostic and
                       (type(diagnostic["severity"]) is not int or diagnostic["severity"] not in range(1, 5)))
                   for diagnostic in result["diagnostics"])):
        raise ValueError("malformed or foreign Lean result")
    if "line" in payload and "goal" not in result:
        raise ValueError("goal response has no goal result")


def submit(url: str, workspace: Path, session: str, path: str, content: str,
           lock: Path, timeout: float, expect_head: str | None = None,
           position: tuple[int, int] | None = None) -> dict:
    workspace = workspace.expanduser().resolve()
    if not (workspace / "scripts/corpus.py").is_file():
        raise ValueError("workspace must name the coordinator-supplied truth-core preview")
    check_id(session, "session")
    if Path(path).is_absolute():
        raise ValueError("--path must be relative to the preview")
    target = file_in(workspace, path)
    payload = {"workspace": str(workspace), "session": session,
               "path": str(target.relative_to(workspace)), "content": content, "timeout": timeout}
    if position is not None:
        if any(value < 0 for value in position):
            raise ValueError("goal positions are zero-based nonnegative integers")
        payload.update(line=position[0], character=position[1])
    url = local_url(url)
    started = time.monotonic()
    with lock.expanduser().open("a") as lease:
        fcntl.flock(lease, fcntl.LOCK_EX)
        acquired = time.monotonic()
        before = revision(workspace)
        if not before["head"]:
            raise ValueError("preview has no Git revision")
        if expect_head and before["head"] != expect_head:
            raise ValueError("preview HEAD differs from --expect-head; obtain the current handoff")
        request = urllib.request.Request(
            url + ("/lean/goal" if position else "/lean/diagnostics"),
            data=json.dumps(payload).encode("utf-8"),
            headers={"Content-Type": "application/json"}, method="POST",
        )
        # Do not inherit HTTP proxy settings or follow a redirect to another service.
        class NoRedirect(urllib.request.HTTPRedirectHandler):
            def redirect_request(self, req, fp, code, msg, headers, newurl):
                return None
        opener = urllib.request.build_opener(urllib.request.ProxyHandler({}), NoRedirect())
        request_started = time.monotonic()
        try:
            with opener.open(request, timeout=timeout + 5) as stream:
                response = json.load(stream)
        except urllib.error.HTTPError as error:
            with error:
                detail = error.read(2000).decode("utf-8", errors="replace")
            raise ValueError(f"service HTTP {error.code}: {detail}") from error
        request_finished = time.monotonic()
        if not isinstance(response, dict):
            raise ValueError("service response must be a JSON object")
        validate_response(response, before, revision(workspace), payload)
    response["client"] = {
        "lease_wait_s": round(acquired - started, 6),
        "request_s": round(request_finished - request_started, 6),
        "total_s": round(time.monotonic() - started, 6),
    }
    return response


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("file", type=Path, help="full UTF-8 content from the canonical worker clone")
    parser.add_argument("--path", required=True, help="unique .lean path relative to the preview")
    parser.add_argument("--workspace", help="coordinator-supplied preview, never inferred from this clone")
    parser.add_argument("--session", help="coordinator-supplied existing Lean session")
    parser.add_argument("--url")
    parser.add_argument("--lock", type=Path)
    parser.add_argument("--expect-head", help="optional exact preview HEAD from the current handoff")
    parser.add_argument("--goal", nargs=2, type=int, metavar=("LINE", "CHARACTER"))
    parser.add_argument("--timeout", type=float, default=120)
    args = parser.parse_args(argv)
    try:
        configured = settings(Path(__file__).resolve().parents[1], dict(os.environ))
        workspace = args.workspace or configured["workspace"]
        session = args.session or configured["session"]
        if not workspace or not session:
            raise ValueError("--workspace and --session (or their documented local settings) are required")
        if not math.isfinite(args.timeout) or args.timeout <= 0:
            raise ValueError("timeout must be finite and positive")
        if args.expect_head and not re.fullmatch(r"[0-9a-f]{40}", args.expect_head):
            raise ValueError("--expect-head must be a full Git commit hash")
        response = submit(
            args.url or configured["url"] or "http://127.0.0.1:8765",
            Path(workspace), session, args.path, args.file.read_text(encoding="utf-8"),
            args.lock or Path(configured["lock"] or Path(tempfile.gettempdir()) / "truth-core-lean.lock"),
            args.timeout, args.expect_head, tuple(args.goal) if args.goal else None,
        )
        print(json.dumps(response, ensure_ascii=False, indent=2))
        return int(any(item.get("severity") == 1 for item in response["result"]["diagnostics"]))
    except (OSError, ValueError, RequestError, urllib.error.URLError) as error:
        print(f"agent_lean: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
