#!/usr/bin/env python3
"""Local agent service: a small HTTP adapter over the corpus CLI and Lean (#489).

The service is an experiment (AGENTS.md, "Local server experiment for the next
workloop"). It adds no proof-status registry and no dependency: corpus
operations run the existing `scripts/corpus.py` commands in the requested
workspace, Lean operations talk to `lake env lean --server` over LSP, and
verification jobs run `lake build`, `corpus.py bind-check` and
`scripts/verify-result.sh` one at a time. Interactive diagnostics do not
replace those checks on the final inputs.

It binds to 127.0.0.1 only. Every response carries a `binding` object: the
workspace path, its git HEAD, a dirty flag, a hash of the uncommitted diff,
and hashes of the request's inputs (for Lean, the exact text elaborated).

    python3 scripts/agent_service.py [--port 8765]

See docs/agent-service.md for the endpoints and client commands.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import os
import queue
import re
import signal
import subprocess
import sys
import threading
import time
import uuid
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import parse_qs, urlparse

ROOT = Path(__file__).resolve().parent.parent
HOST = "127.0.0.1"
RECORD_DIRS = (
    "statements",
    "claims",
    "arguments",
    "inferences",
    "results",
    "definitions",
    "disambiguations",
    "passages",
    "sources",
    "relations",
    "candidates",
    "attempts",
    "configurations",
    "models",
)
ID_RE = re.compile(r"^[A-Za-z0-9][A-Za-z0-9._-]*$")
OUTPUT_LIMIT = 200_000


class RequestError(Exception):
    def __init__(self, status: int, message: str):
        super().__init__(message)
        self.status = status


def sha256(data: str | bytes) -> str:
    if isinstance(data, str):
        data = data.encode("utf-8")
    return hashlib.sha256(data).hexdigest()


def git(workspace: Path, *args: str) -> str:
    return subprocess.run(
        ["git", *args], cwd=workspace, capture_output=True, text=True, check=False
    ).stdout


def revision(workspace: Path) -> dict:
    """HEAD, dirty flag and a hash of the uncommitted state of `workspace`."""
    head = git(workspace, "rev-parse", "HEAD").strip() or None
    status = git(workspace, "status", "--porcelain", "--untracked-files=all")
    dirty = bool(status.strip())
    state = {"workspace": str(workspace), "head": head, "dirty": dirty}
    if dirty:
        state["diff_sha256"] = sha256(git(workspace, "diff", "HEAD", "--binary") + "\0" + status)
    return state


def check_id(value: str | None, name: str) -> str:
    if not value or not ID_RE.match(value):
        raise RequestError(400, f"missing or malformed {name}")
    return value


class Workspaces:
    """Resolve the `workspace` parameter to a checkout directory."""

    def __init__(self, default: Path):
        self.default = default.resolve()

    def resolve(self, value: str | None) -> Path:
        path = Path(value).expanduser().resolve() if value else self.default
        if not (path / "scripts" / "corpus.py").is_file():
            raise RequestError(400, f"not a truth-core checkout: {path}")
        return path


def file_in(workspace: Path, relative: str | None) -> Path:
    if not relative:
        raise RequestError(400, "missing path")
    path = (workspace / relative).resolve()
    if workspace not in path.parents or path.suffix != ".lean":
        raise RequestError(400, f"path must be a .lean file inside the workspace: {relative}")
    return path


# --- corpus -----------------------------------------------------------------


def run_corpus(workspace: Path, args: list[str], timeout: float = 300) -> dict:
    proc = subprocess.run(
        [sys.executable, "scripts/corpus.py", *args],
        cwd=workspace,
        capture_output=True,
        text=True,
        timeout=timeout,
        check=False,
    )
    out: dict = {"command": ["python3", "scripts/corpus.py", *args], "returncode": proc.returncode}
    if "--json" in args and proc.returncode == 0:
        out["data"] = json.loads(proc.stdout)
    else:
        out["stdout"] = proc.stdout[-OUTPUT_LIMIT:]
    out["stderr"] = proc.stderr[-OUTPUT_LIMIT:]
    return out


def find_record(workspace: Path, record_id: str) -> dict:
    corpus = workspace / "corpus"
    for kind in RECORD_DIRS:
        for path in sorted((corpus / kind).glob("*.json")):
            text = path.read_text(encoding="utf-8")
            if f'"{record_id}"' not in text:
                continue
            record = json.loads(text)
            if isinstance(record, dict) and record.get("id") == record_id:
                return {
                    "kind": kind,
                    "path": str(path.relative_to(workspace)),
                    "file_sha256": sha256(text),
                    "record": record,
                }
    raise RequestError(404, f"no corpus record with id {record_id}")


# --- Lean LSP sessions -------------------------------------------------------


class LeanSession:
    """One `lake env lean --server` process for one (workspace, session id)."""

    def __init__(self, workspace: Path, name: str, command: list[str]):
        self.workspace = workspace
        self.name = name
        self.lock = threading.Lock()  # one request at a time per session
        self.versions: dict[str, int] = {}
        self.texts: dict[str, str] = {}
        self.diagnostics: dict[str, dict] = {}
        self.pending: dict[int, dict] = {}
        self.ids = itertools.count(1)
        self.write_lock = threading.Lock()
        self.cond = threading.Condition()
        self.started = time.time()
        self.proc = subprocess.Popen(
            command,
            cwd=workspace,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL,
            start_new_session=True,  # close() ends lake and its lean children together
        )
        threading.Thread(target=self._read_loop, daemon=True).start()
        self.request(
            "initialize",
            {
                "processId": None,
                "rootUri": workspace.as_uri(),
                "capabilities": {},
            },
            timeout=120,
        )
        self.notify("initialized", {})

    # transport
    def _send(self, message: dict) -> None:
        body = json.dumps(message).encode("utf-8")
        with self.write_lock:
            assert self.proc.stdin is not None
            self.proc.stdin.write(f"Content-Length: {len(body)}\r\n\r\n".encode("ascii") + body)
            self.proc.stdin.flush()

    def _read_loop(self) -> None:
        stream = self.proc.stdout
        assert stream is not None
        while True:
            length = None
            while True:
                line = stream.readline()
                if not line:
                    with self.cond:
                        self.cond.notify_all()
                    return
                line = line.strip()
                if not line:
                    break
                if line.lower().startswith(b"content-length:"):
                    length = int(line.split(b":", 1)[1])
            if length is None:
                continue
            message = json.loads(stream.read(length))
            self._dispatch(message)

    def _dispatch(self, message: dict) -> None:
        if "id" in message and "method" in message:
            # A server-to-client request (e.g. client/registerCapability): accept it.
            self._send({"jsonrpc": "2.0", "id": message["id"], "result": None})
            return
        with self.cond:
            if "id" in message:
                self.pending[message["id"]] = message
            elif message.get("method") == "textDocument/publishDiagnostics":
                params = message["params"]
                self.diagnostics[params["uri"]] = params
            self.cond.notify_all()

    def notify(self, method: str, params: dict) -> None:
        self._send({"jsonrpc": "2.0", "method": method, "params": params})

    def request(self, method: str, params: dict, timeout: float = 600) -> object:
        request_id = next(self.ids)
        self._send({"jsonrpc": "2.0", "id": request_id, "method": method, "params": params})
        deadline = time.time() + timeout
        with self.cond:
            while request_id not in self.pending:
                if self.proc.poll() is not None:
                    raise RequestError(502, f"Lean server exited ({self.proc.returncode})")
                remaining = deadline - time.time()
                if remaining <= 0:
                    raise RequestError(504, f"Lean request {method} timed out")
                self.cond.wait(remaining)
            response = self.pending.pop(request_id)
        if "error" in response:
            raise RequestError(502, f"Lean {method}: {response['error']}")
        return response.get("result")

    # documents
    def sync(self, path: Path, text: str, timeout: float) -> dict:
        """Open or update `path` with `text`; wait for and return its diagnostics."""
        uri = path.as_uri()
        if uri not in self.versions:
            self.versions[uri] = 1
            self.notify(
                "textDocument/didOpen",
                {"textDocument": {"uri": uri, "languageId": "lean4", "version": 1, "text": text}},
            )
        elif self.texts.get(uri) != text:
            self.versions[uri] += 1
            self.notify(
                "textDocument/didChange",
                {
                    "textDocument": {"uri": uri, "version": self.versions[uri]},
                    "contentChanges": [{"text": text}],
                },
            )
        self.texts[uri] = text
        version = self.versions[uri]
        self.request("textDocument/waitForDiagnostics", {"uri": uri, "version": version}, timeout)
        with self.cond:
            published = self.diagnostics.get(uri, {})
        return {
            "uri": uri,
            "version": version,
            "diagnostics": published.get("diagnostics", []) if published.get("version", version) == version else [],
        }

    def goal(self, path: Path, line: int, character: int, timeout: float) -> object:
        params = {"textDocument": {"uri": path.as_uri()}, "position": {"line": line, "character": character}}
        return {
            "plainGoal": self.request("$/lean/plainGoal", params, timeout),
            "plainTermGoal": self.request("$/lean/plainTermGoal", params, timeout),
        }

    def close(self) -> None:
        try:
            self.request("shutdown", {}, timeout=10)
            self.notify("exit", {})
            assert self.proc.stdin is not None
            self.proc.stdin.close()
            self.proc.wait(timeout=10)
        except Exception:
            pass
        try:
            os.killpg(self.proc.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        self.proc.wait()

    def describe(self) -> dict:
        return {
            "workspace": str(self.workspace),
            "session": self.name,
            "alive": self.proc.poll() is None,
            "open_files": {uri: self.versions[uri] for uri in sorted(self.versions)},
            "uptime_s": round(time.time() - self.started, 1),
        }


class LeanSessions:
    def __init__(self, command: list[str]):
        self.command = command
        self.sessions: dict[tuple[str, str], LeanSession] = {}
        self.lock = threading.Lock()

    def get(self, workspace: Path, name: str, create: bool = True) -> LeanSession:
        key = (str(workspace), name)
        with self.lock:
            session = self.sessions.get(key)
            if session is not None and session.proc.poll() is not None:
                del self.sessions[key]
                session = None
            if session is None:
                if not create:
                    raise RequestError(404, f"no Lean session {name} for {workspace}")
                session = LeanSession(workspace, name, self.command)
                self.sessions[key] = session
            return session

    def close(self, workspace: Path, name: str) -> bool:
        with self.lock:
            session = self.sessions.pop((str(workspace), name), None)
        if session:
            session.close()
        return session is not None

    def close_all(self) -> None:
        with self.lock:
            sessions = list(self.sessions.values())
            self.sessions.clear()
        for session in sessions:
            session.close()


# --- verification job queue ---------------------------------------------------


def job_command(kind: str, body: dict) -> list[str]:
    if kind == "build":
        targets = body.get("targets") or []
        for target in targets:
            check_id(target, "build target")
        return ["lake", "build", *targets]
    if kind == "bind-check":
        return [sys.executable, "scripts/corpus.py", "bind-check"]
    if kind == "verify-result":
        return ["scripts/verify-result.sh", check_id(body.get("result_id"), "result_id")]
    raise RequestError(400, f"unknown job kind {kind!r}; expected build, bind-check or verify-result")


class JobQueue:
    """Run expensive verification jobs one at a time, in submission order."""

    def __init__(self):
        self.jobs: dict[str, dict] = {}
        self.queue: queue.Queue[str] = queue.Queue()
        self.lock = threading.Lock()
        threading.Thread(target=self._worker, daemon=True).start()

    def submit(self, workspace: Path, kind: str, body: dict) -> dict:
        command = job_command(kind, body)
        job_id = uuid.uuid4().hex[:12]
        job = {
            "id": job_id,
            "kind": kind,
            "command": command,
            "status": "queued",
            "submitted": time.time(),
            "workspace": workspace,
            "binding_at_submit": revision(workspace),
        }
        with self.lock:
            self.jobs[job_id] = job
        self.queue.put(job_id)
        return self.view(job_id)

    def view(self, job_id: str) -> dict:
        with self.lock:
            job = self.jobs.get(job_id)
            if job is None:
                raise RequestError(404, f"no job {job_id}")
            out = {k: v for k, v in job.items() if k != "workspace"}
            out["position"] = (
                sum(1 for j in self.jobs.values() if j["status"] == "queued" and j["submitted"] < job["submitted"])
                if job["status"] == "queued"
                else None
            )
            return out

    def _worker(self) -> None:
        while True:
            job_id = self.queue.get()
            with self.lock:
                job = self.jobs[job_id]
                job["status"] = "running"
                job["started"] = time.time()
            proc = subprocess.run(
                job["command"], cwd=job["workspace"], capture_output=True, text=True, check=False
            )
            finished = revision(job["workspace"])
            with self.lock:
                job["status"] = "passed" if proc.returncode == 0 else "failed"
                job["returncode"] = proc.returncode
                job["output"] = (proc.stdout + proc.stderr)[-OUTPUT_LIMIT:]
                job["finished"] = time.time()
                job["duration_s"] = round(job["finished"] - job["started"], 2)
                job["binding_at_finish"] = finished
                # A job only certifies the inputs it ran on.
                job["inputs_changed_during_job"] = finished != job["binding_at_submit"]


# --- HTTP ---------------------------------------------------------------------


class Service:
    def __init__(self, default_workspace: Path, lean_command: list[str]):
        self.workspaces = Workspaces(default_workspace)
        self.lean = LeanSessions(lean_command)
        self.jobs = JobQueue()
        self.toolchain = (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip()

    def handle(self, method: str, url: str, body: dict) -> tuple[int, dict]:
        parsed = urlparse(url)
        query = {k: v[-1] for k, v in parse_qs(parsed.query).items()}
        params = {**query, **body}
        route = parsed.path.rstrip("/") or "/"
        workspace = self.workspaces.resolve(params.get("workspace"))
        inputs: dict = {}
        result = self.route(method, route, params, workspace, inputs)
        binding = revision(workspace)
        binding["inputs"] = inputs
        return 200, {"binding": binding, "result": result}

    def route(self, method: str, route: str, params: dict, workspace: Path, inputs: dict) -> object:
        if method == "GET" and route == "/health":
            return {"status": "ok", "toolchain": self.toolchain, "lean_command": self.lean.command}
        if method == "GET" and route == "/corpus/record":
            inputs["id"] = check_id(params.get("id"), "id")
            found = find_record(workspace, inputs["id"])
            inputs["file_sha256"] = found["file_sha256"]
            return found
        if method == "GET" and route == "/corpus/dossier":
            inputs["id"] = check_id(params.get("id"), "id")
            return run_corpus(workspace, ["dossier", "--json", inputs["id"]])
        if method == "GET" and route == "/corpus/frontier":
            args = ["frontier", "--json"]
            if params.get("root"):
                args += ["--root", check_id(params["root"], "root")]
            if truthy(params.get("reaching_root")):
                args.append("--reaching-root")
            if truthy(params.get("routes")):
                args = [a for a in args if a != "--json"] + ["--routes"]
            inputs["args"] = args
            return run_corpus(workspace, args)
        if method == "POST" and route == "/corpus/check":
            return run_corpus(workspace, ["check"])
        if method == "POST" and route in ("/lean/diagnostics", "/lean/goal"):
            return self.lean_route(route, params, workspace, inputs)
        if method == "GET" and route == "/lean/sessions":
            with self.lean.lock:
                return [s.describe() for s in self.lean.sessions.values()]
        if method == "POST" and route == "/lean/close":
            return {"closed": self.lean.close(workspace, check_id(params.get("session"), "session"))}
        if method == "POST" and route == "/jobs":
            job = self.jobs.submit(workspace, str(params.get("kind")), params)
            inputs["command"] = job["command"]
            return job
        if method == "GET" and route.startswith("/jobs/"):
            job = self.jobs.view(route.removeprefix("/jobs/"))
            inputs["command"] = job["command"]
            return job
        raise RequestError(404, f"no route {method} {route}")

    def lean_route(self, route: str, params: dict, workspace: Path, inputs: dict) -> object:
        name = check_id(params.get("session", "default"), "session")
        path = file_in(workspace, params.get("path"))
        text = params.get("content")
        if text is None:
            if not path.is_file():
                raise RequestError(404, f"no file {path}")
            text = path.read_text(encoding="utf-8")
        timeout = float(params.get("timeout", 600))
        inputs.update(
            session=name,
            path=str(path.relative_to(workspace)),
            content_source="request" if "content" in params else "disk",
            content_sha256=sha256(text),
        )
        session = self.lean.get(workspace, name)
        with session.lock:
            started = time.time()
            out = session.sync(path, text, timeout)
            if route == "/lean/goal":
                line, character = int(params["line"]), int(params["character"])
                inputs.update(line=line, character=character)
                out["goal"] = session.goal(path, line, character, timeout)
            out["elapsed_s"] = round(time.time() - started, 3)
        return out


def truthy(value: object) -> bool:
    return str(value).lower() in ("1", "true", "yes")


def make_handler(service: Service, log: bool = True):
    class Handler(BaseHTTPRequestHandler):
        def _respond(self, method: str) -> None:
            try:
                length = int(self.headers.get("Content-Length") or 0)
                raw = self.rfile.read(length) if length else b""
                body = json.loads(raw) if raw else {}
                if not isinstance(body, dict):
                    raise RequestError(400, "request body must be a JSON object")
                status, payload = service.handle(method, self.path, body)
            except RequestError as error:
                status, payload = error.status, {"error": str(error)}
            except (ValueError, KeyError) as error:
                status, payload = 400, {"error": f"bad request: {error}"}
            except subprocess.TimeoutExpired as error:
                status, payload = 504, {"error": f"timed out: {error}"}
            data = json.dumps(payload, ensure_ascii=False, indent=1).encode("utf-8")
            self.send_response(status)
            self.send_header("Content-Type", "application/json; charset=utf-8")
            self.send_header("Content-Length", str(len(data)))
            self.end_headers()
            self.wfile.write(data)

        def do_GET(self) -> None:  # noqa: N802
            self._respond("GET")

        def do_POST(self) -> None:  # noqa: N802
            self._respond("POST")

        def log_message(self, format: str, *args: object) -> None:  # noqa: A002
            if log:
                sys.stderr.write(f"agent_service: {format % args}\n")

    return Handler


def serve(
    port: int, workspace: Path, lean_command: list[str], log: bool = True
) -> tuple[ThreadingHTTPServer, Service]:
    service = Service(workspace, lean_command)
    server = ThreadingHTTPServer((HOST, port), make_handler(service, log))
    server.daemon_threads = True
    return server, service


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--port", type=int, default=8765)
    parser.add_argument("--workspace", type=Path, default=ROOT, help="default checkout (default: this one)")
    parser.add_argument(
        "--lean-command",
        default="lake env lean --server",
        help="Lean language server command, run in each workspace",
    )
    args = parser.parse_args(argv)
    server, service = serve(args.port, args.workspace, args.lean_command.split())
    print(f"agent_service: listening on http://{HOST}:{server.server_address[1]}", flush=True)

    def stop(signum: int, frame: object) -> None:
        raise KeyboardInterrupt

    signal.signal(signal.SIGTERM, stop)  # shut Lean sessions down on `kill` too
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass
    finally:
        service.lean.close_all()
        server.server_close()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
