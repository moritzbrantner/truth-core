#!/usr/bin/env python3
"""Set a worker environment; run --check once, then -- <command> without preflight."""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
BINARIES = (
    'rust-target/release/truth-core-comparator',
    'lean4export/.lake/build/bin/lean4export',
    'bin/landrun',
    'nanoda_lib/target/release/nanoda_bin',
)


def git(root, *args, optional=False):
    result = subprocess.run(['git', *args], cwd=root, text=True, capture_output=True)
    if result.returncode and not (optional and result.returncode == 1):
        raise ValueError(result.stderr.strip() or 'git command failed')
    return result.stdout.strip()


def environment(root, inherited):
    env = dict(inherited)
    home = Path(env.get('HOME') or Path.home())
    value = env.get('TRUTH_CORE_VERIFIER_HOME') or git(
        root, 'config', '--local', '--get', 'truthcore.verifierHome', optional=True)
    cache = Path(value).expanduser() if value else home / '.cache/truth-core-verifier'
    if not cache.is_absolute():
        cache = root / cache
    env['TRUTH_CORE_VERIFIER_HOME'] = str(cache.resolve())
    elan = str(home / '.elan/bin')
    env['PATH'] = elan + (os.pathsep + env['PATH'] if env.get('PATH') else '')
    return env


def check_environment(root, env, lean_version=False):
    pin = ''.join((root / 'lean-toolchain').read_text().split())
    if not pin:
        raise ValueError('empty repository lean-toolchain')
    cache = Path(env['TRUTH_CORE_VERIFIER_HOME'])
    exporter_pin = ''.join((cache / 'lean4export/lean-toolchain').read_text().split())
    if exporter_pin != pin:
        raise ValueError(f'exporter toolchain {exporter_pin!r} differs from repository {pin!r}')
    for name in BINARIES:
        path = cache / name
        if not path.is_file() or not os.access(path, os.X_OK):
            raise ValueError(f'missing executable: {path}')
    if lean_version:
        release = re.fullmatch(r'leanprover/lean4:v(.+)', pin)
        if not release:
            raise ValueError('--lean-version requires a Lean release pin')
        output = subprocess.check_output(
            ['elan', 'run', pin, 'lean', '--version'],
            cwd=root, env=env, text=True, timeout=10)
        found = re.search(r'\bversion\s+([^\s,]+)', output)
        if not found or found[1] != release[1]:
            raise ValueError(f'lean --version does not match {pin}: {output.strip()}')
    return {'workspace': str(root), 'head': git(root, 'rev-parse', 'HEAD'),
            'toolchain': pin, 'verifier_home': str(cache)}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true', help='one startup preflight')
    parser.add_argument('--lean-version', action='store_true', help='also check lean --version')
    parser.add_argument('command', nargs=argparse.REMAINDER)
    args = parser.parse_args(argv)
    command = args.command[1:] if args.command[:1] == ['--'] else args.command
    if args.check and command:
        parser.error('--check does not run a command')
    if args.lean_version and not args.check:
        parser.error('--lean-version requires --check')
    if not args.check and not command:
        parser.error('use --check or -- <command>')
    try:
        env = environment(ROOT, os.environ)
        if args.check:
            print(json.dumps(check_environment(ROOT, env, args.lean_version)))
            return 0
        os.execvpe(command[0], command, env)
    except (OSError, ValueError, subprocess.SubprocessError) as exc:
        print(f'worker_env: {exc}', file=sys.stderr)
        return 2


if __name__ == '__main__':
    sys.exit(main())
