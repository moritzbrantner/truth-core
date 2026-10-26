#!/usr/bin/env python3
"""Prepare an explicitly selected standalone worker clone; never verify proofs."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shlex
import shutil
import subprocess
import sys
import time
from datetime import datetime, timezone


def run(root, *command, capture=False):
    print(f"+ (cd {shlex.quote(str(root))} && {shlex.join(command)})", flush=True)
    started = time.monotonic()
    try:
        return subprocess.run(command, cwd=root, check=True, text=True,
                              stdout=subprocess.PIPE if capture else None,
                              timeout=3600).stdout
    finally:
        print(f"elapsed={time.monotonic() - started:.3f}s", flush=True)


def worker_clone(path):
    root = Path(path).absolute()
    if root != root.resolve() or root == Path.home() or root == Path(root.anchor):
        raise ValueError("--clone must be a real clone path, not a symlink, home or filesystem root")
    if not (root / ".git").is_dir() or (root / ".git").is_symlink():
        raise ValueError("--clone must contain its own .git directory (worktrees are unsupported)")
    top = run(root, "git", "rev-parse", "--show-toplevel", capture=True).strip()
    if Path(top).resolve() != root:
        raise ValueError("--clone must name the repository root")
    remote = run(root, "git", "remote", "get-url", "origin", capture=True).strip()
    if not re.fullmatch(r"(?:https://github\.com/|git@github\.com:)moritzbrantner/truth-core(?:\.git)?", remote):
        raise ValueError("expected the truth-core origin; local shared-cache clones must set their upstream origin first")
    for required in ("lean-toolchain", "lake-manifest.json", "bun.lock", "scripts/bootstrap-verifier.sh"):
        if not (root / required).is_file():
            raise ValueError(f"missing repository input: {required}")
    return root


def install_paths(root):
    manifest = json.loads((root / "package.json").read_text())
    paths = [root / "node_modules"]
    for pattern in manifest["workspaces"]:
        for workspace in sorted(root.glob(pattern)):
            if (workspace / "package.json").is_file():
                paths.append(workspace / "node_modules")
    # Validate all paths before removing any one of them. Never follow symlinks.
    for path in paths:
        if path.is_symlink() or path.parent.resolve() != path.parent or not path.is_relative_to(root):
            raise ValueError(f"unsafe disposable install path: {path}")
        tracked = run(root, "git", "ls-files", "--", str(path.relative_to(root)), capture=True)
        if tracked.strip():
            raise ValueError(f"install path contains tracked files: {path}")
    return paths


def digest_files(paths):
    digest = hashlib.sha256()
    for path in sorted(paths):
        digest.update(str(path).encode())
        digest.update(path.read_bytes())
    return digest.hexdigest()


def install_digest(paths):
    """Detect missing/changed installed entries, including Bun's executable links."""
    entries = []
    for root in paths:
        if not root.is_dir():
            entries.append((str(root), "missing"))
            continue
        for folder, directories, files in os.walk(root, followlinks=False):
            for name in sorted(directories + files):
                path = Path(folder) / name
                stat = path.lstat()
                entries.append((str(path), stat.st_mode, stat.st_size, stat.st_mtime_ns,
                                os.readlink(path) if path.is_symlink() else ""))
    return hashlib.sha256(json.dumps(sorted(entries)).encode()).hexdigest()


def reconcile(root, name, inputs, output, action):
    # Two dependency readiness entries only; this file records no gate/proof success.
    path = root / ".git/truth-core-preparation.json"
    state = json.loads(path.read_text()) if path.exists() else {}
    before = {"inputs": inputs, "output": output()}
    if before["output"] is not None and state.get(name) == before:
        print(f"unchanged: {name} inputs and installed artifacts verified", flush=True)
        return
    action()
    verified = output()
    if verified is None:
        raise ValueError(f"{name} preparation did not produce required artifacts")
    state[name] = {"inputs": inputs, "output": verified}
    temporary = path.with_suffix(".tmp")
    temporary.write_text(json.dumps(state, sort_keys=True) + "\n")
    temporary.replace(path)
    print(f"changed: {name} reconciled", flush=True)


def prepare_bun(root):
    paths = install_paths(root)
    if any((path / ".bun").exists() or (path / ".bun").is_symlink() for path in paths):
        for path in paths:
            if path.exists():
                print(f"remove stale disposable install: {path.relative_to(root)}", flush=True)
                shutil.rmtree(path)
    inputs = digest_files([root / "bun.lock", root / "package.json", Path(__file__),
                           *[path.parent / "package.json" for path in paths[1:]]])
    inputs += run(root, "bun", "--version", capture=True).strip()
    # Explicit config bypasses a user's isolated-linker setting without changing it.
    reconcile(root, "bun", inputs, lambda: install_digest(paths) if paths[0].is_dir() else None,
              lambda: run(root, "bun", "--config=/dev/null", "install", "--linker=hoisted", "--frozen-lockfile"))


def check_packages(root, acquiring=False):
    manifest = json.loads((root / "lake-manifest.json").read_text())
    for package in manifest["packages"]:
        path = root / manifest["packagesDir"] / package["name"]
        if package["type"] != "git" or not path.resolve().is_relative_to(root):
            raise ValueError(f"unsupported dependency boundary: {package['name']}")
        if acquiring and not path.exists():
            continue
        revision = run(path, "git", "rev-parse", "HEAD", capture=True).strip()
        if revision != package["rev"] and not acquiring:
            raise ValueError(f"dependency revision mismatch: {package['name']}")
        if run(path, "git", "status", "--porcelain", "--untracked-files=no", capture=True).strip():
            raise ValueError(f"modified pinned dependency: {package['name']}")


def prepare_verifier(root):
    work = Path(os.environ.get("TRUTH_CORE_VERIFIER_HOME", str(Path.home() / ".cache/truth-core-verifier")))
    binaries = [work / name for name in ("rust-target/release/truth-core-comparator",
                "lean4export/.lake/build/bin/lean4export", "bin/landrun",
                "nanoda_lib/target/release/nanoda_bin")]
    inputs = digest_files([root / "lean-toolchain", root / "scripts/verifier-pins.env",
                          root / "scripts/bootstrap-verifier.sh", Path(__file__),
                          root / "verifier/Cargo.toml", root / "verifier/Cargo.lock",
                          *list((root / "verifier/src").rglob("*.rs"))])
    for tool in ("cargo", "rustc", "go", "lean"):
        inputs += run(root, tool, "version" if tool == "go" else "--version", capture=True)

    inputs += json.dumps({key: os.environ.get(key) for key in (
        "RUSTFLAGS", "CARGO_ENCODED_RUSTFLAGS", "RUSTUP_TOOLCHAIN",
        "GOFLAGS", "GOOS", "GOARCH", "CGO_ENABLED")}, sort_keys=True)

    def output():
        sources = ""
        for name in ("lean4export", "landrun", "nanoda_lib"):
            directory = work / name
            if not directory.exists():
                continue
            sources += run(directory, "git", "rev-parse", "HEAD", capture=True)
            if run(directory, "git", "status", "--porcelain", "--untracked-files=no", capture=True).strip():
                raise ValueError(f"modified verifier source: {directory}")
        if not all(path.is_file() and os.access(path, os.X_OK) for path in binaries):
            return None
        sources += (work / "lean4export/lean-toolchain").read_text()
        return digest_files(binaries) + sources

    reconcile(root, "verifier", inputs, output, lambda: run(root, "scripts/bootstrap-verifier.sh"))


def prepare(root):
    for tool in ("git", "lean", "lake", "cargo", "rustc", "go", "bun"):
        if shutil.which(tool) is None:
            raise ValueError(f"missing required build tool: {tool}")
    expected = (root / "lean-toolchain").read_text().strip().split(":")[-1].removeprefix("v")
    actual = run(root, "lean", "--version", capture=True)
    if f"version {expected}," not in actual:
        raise ValueError(f"Lean does not match lean-toolchain: {actual.strip()}")
    # Lake acquires the manifest-pinned packages and Mathlib's hash-validated oleans.
    # This must precede project compilation; no project build is hidden in startup.
    check_packages(root, acquiring=True)
    run(root, "lake", "exe", "cache", "get")
    check_packages(root)
    prepare_verifier(root)
    prepare_bun(root)
    print("ready: dependencies prepared; source/Lean/Comparator verification still required", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--clone", required=True, help="explicit standalone clone whose install directories are disposable")
    args = parser.parse_args()
    started = time.monotonic()
    print(f"started_utc={datetime.now(timezone.utc).isoformat()}", flush=True)
    try:
        prepare(worker_clone(args.clone))
    except (ValueError, OSError, subprocess.SubprocessError) as error:
        print(f"preparation failed: {error}", file=sys.stderr)
        return 1
    finally:
        print(f"finished_utc={datetime.now(timezone.utc).isoformat()} elapsed={time.monotonic() - started:.3f}s", flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
