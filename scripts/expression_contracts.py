"""Reviewed, bounded exact-expression contracts; no philosophical verdicts.

Snapshots originate in isolated frozen Challenge extraction. No command in this
module rewrites them. Alpha names/metadata are ignored by Lean's encoding;
complete dependent telescope/application expressions are otherwise exact.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path

DIRECTORY = Path(__file__).resolve().parent / 'contracts'


def fingerprint(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':'), ensure_ascii=False).encode()).hexdigest()


def contracts():
    return {item['result_id']: item for path in sorted(DIRECTORY.glob('*.json'))
            for item in [json.loads(path.read_text())]}


def selected_theorems(results):
    registered = contracts()
    return [r['theorem'] for r in results if r['id'] in registered]


def summarize(expression):
    if expression.get('encoding') != 'closed-expression-v1':
        raise ValueError('unsupported or missing closed-expression encoding')
    if 'unsupported-' in json.dumps(expression):
        raise ValueError('unsupported expression boundary in exact contract')
    dependencies = expression.get('dependencies')
    if not isinstance(dependencies, list) or len({d['declaration'] for d in dependencies}) != len(dependencies):
        raise ValueError('missing or duplicated expression dependencies')
    return {'type_sha256': fingerprint([expression['universe_parameters'], expression['type']]),
            'dependencies': {d['declaration']: fingerprint(d) for d in dependencies}}


def check(result, described, root):
    contract = contracts().get(result['id'])
    if contract is None:
        return []
    problems = []
    if result['theorem'] != contract['theorem']:
        problems.append({'kind': 'expression-contract-theorem', 'expected': contract['theorem']})
    for item in contract['frozen_inputs']:
        path = root / item['path']
        if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != item['sha256']:
            problems.append({'kind': 'expression-contract-frozen-input', 'path': item['path']})
    try:
        actual = summarize(described.get('expression_contract', {}))
    except (ValueError, KeyError, TypeError) as exc:
        return problems + [{'kind': 'expression-contract-unavailable', 'detail': str(exc)}]
    if actual['type_sha256'] != contract['type_sha256']:
        problems.append({'kind': 'expression-contract-type', 'expected': contract['type_sha256'],
                         'actual': actual['type_sha256']})
    expected, current = contract['dependencies'], actual['dependencies']
    changed = sorted(n for n in expected.keys() | current.keys() if expected.get(n) != current.get(n))
    if changed:
        problems.append({'kind': 'expression-contract-dependencies', 'declarations': changed})
    return problems


def main(argv=None):
    """Reproduce preservation evidence without rewriting the reviewed snapshot."""
    import argparse
    import os
    import subprocess
    import tempfile

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('result_id', choices=sorted(contracts()))
    args = parser.parse_args(argv)
    root = DIRECTORY.parents[1]
    record = json.loads((root / 'corpus/results' / f'{args.result_id}.json').read_text())
    challenge = root / (record['challenge_module'].replace('.', '/') + '.lean')
    theorem = record['theorem']
    run = ['python3', 'scripts/worker_env.py', '--', 'lake', 'env', 'lean']

    def extract(module, directory=None):
        request = {'modules': [module], 'theorems': [theorem], 'contract_theorems': [theorem]}
        with tempfile.NamedTemporaryFile('w', suffix='.json') as handle:
            json.dump(request, handle)
            handle.flush()
            env = dict(os.environ)
            if directory is not None:
                env['LEAN_PATH'] = str(directory) + os.pathsep + env.get('LEAN_PATH', '')
            completed = subprocess.run(run + ['--run', 'scripts/BindTypes.lean', handle.name],
                cwd=root, env=env, capture_output=True, text=True, check=True)
        return json.loads(completed.stdout)[0]

    try:
        # The same theorem name belongs to the Challenge and Solution. Isolated
        # imports are essential: importing both would conflate their evidence.
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            source = directory / 'FrozenContract.lean'
            source.write_bytes(challenge.read_bytes())
            subprocess.run(run + [f'--root={directory}', '-o', str(directory / 'FrozenContract.olean'), str(source)],
                cwd=root, capture_output=True, text=True, check=True)
            frozen = extract('FrozenContract', directory)
        current = extract(record['solution_module'])
        failures = {'challenge': check(record, frozen, root), 'solution': check(record, current, root)}
        print(json.dumps({'result_id': args.result_id, 'preservation': not any(failures.values()),
            'method': 'alpha-canonical complete type and reviewed dependency identity',
            'dependencies': len(summarize(current['expression_contract'])['dependencies']), 'failures': failures}, indent=2))
        return int(any(failures.values()))
    except (subprocess.CalledProcessError, OSError, ValueError, KeyError) as exc:
        print(json.dumps({'result_id': args.result_id, 'preservation': False, 'error': str(exc),
            'diagnostics': getattr(exc, 'stdout', '') + getattr(exc, 'stderr', '')}))
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
