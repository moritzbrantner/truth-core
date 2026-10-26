"""Explicit finite interpretations; registrations never participate in closure."""
from __future__ import annotations

from itertools import combinations
from pathlib import Path
import re
import subprocess
import tempfile

TERM = re.compile(r"[A-Za-z_][A-Za-z_0-9]*(?:\.(?:[A-Za-z_][A-Za-z_0-9]*|[0-9]+))*")
NAME = re.compile(r"[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*")


def validate_model(model, statements, root):
    def name(value):
        return isinstance(value, str) and NAME.fullmatch(value)
    if not isinstance(model.get('id'), str) or not re.fullmatch(r'MODEL-[A-Z0-9-]+', model['id']):
        raise ValueError('model id must be MODEL-…')
    for key in ('description', 'vocabulary', 'lean_declaration'):
        if not isinstance(model.get(key), str) or not model[key]:
            raise ValueError(f'missing {key}')
    if not name(model['lean_declaration']):
        raise ValueError('invalid model Lean declaration')
    modules = model.get('modules')
    if not isinstance(modules, list) or not modules or any(not name(m) for m in modules) or len(set(modules)) != len(modules):
        raise ValueError('modules must be a nonempty unique list')
    for module in modules:
        if not name(module) or not (root / (module.replace('.', '/') + '.lean')).is_file():
            raise ValueError(f'unknown module {module}')
    bindings = model.get('bindings')
    if not isinstance(bindings, dict) or not bindings or any(not name(k) or not isinstance(v, str) or not TERM.fullmatch(v) for k, v in bindings.items()):
        raise ValueError('bindings must name nonempty Lean terms')
    carriers = model.get('carriers')
    if not isinstance(carriers, list) or not carriers:
        raise ValueError('carriers must be nonempty')
    for carrier in carriers:
        if not isinstance(carrier, dict) or not isinstance(carrier.get('binding'), str) or carrier.get('binding') not in bindings or not name(carrier.get('theorem')):
            raise ValueError('carrier needs a binding and enumeration theorem')
        elements = carrier.get('elements')
        if not isinstance(elements, list) or not elements or len(set(elements)) != len(elements) or any(not name(x) for x in elements):
            raise ValueError('carrier elements must be nonempty unique Lean terms')
    seen = set()
    evaluations = model.get('evaluations')
    if not isinstance(evaluations, list) or not evaluations:
        raise ValueError('evaluations must be nonempty')
    for evaluation in evaluations:
        if not isinstance(evaluation, dict):
            raise ValueError('evaluation must be an object')
        sid = evaluation.get('statement_id')
        if not isinstance(sid, str) or sid not in statements or not name(statements[sid].get('lean_declaration')):
            raise ValueError(f'unknown or unbound statement {sid}')
        if sid in seen:
            raise ValueError(f'duplicate/conflicting evaluation {sid}')
        seen.add(sid)
        if not isinstance(evaluation.get('value'), str) or evaluation.get('value') not in ('satisfies', 'violates') or not name(evaluation.get('theorem')):
            raise ValueError('evaluation needs satisfies/violates and a theorem declaration')
        args = evaluation.get('arguments')
        if not isinstance(args, list) or any(not isinstance(arg, str) or arg not in bindings for arg in args):
            raise ValueError(f'evaluation {sid} arguments must reference registered bindings')


def certificate_source(models, statements):
    """Compiler checks the *exact* closed statement application and enumeration."""
    lines = [f'import {m}' for m in sorted({m for model in models for m in model['modules']})]
    lines += ['namespace FiniteModelCertificates']
    names = []
    for i, model in enumerate(models):
        bindings = model['bindings']
        # Reject a nonexistent registered model even if evaluations do not use it.
        n = f'interpretation_{i}'
        lines += [f'def {n} := @{model["lean_declaration"]}']
        names.append(n)
        for j, carrier in enumerate(model['carriers']):
            alternatives = ' ∨ '.join(f'x = ({element})' for element in carrier['elements'])
            n = f'carrier_{i}_{j}'
            lines += [f'theorem {n} : ∀ x : ({bindings[carrier["binding"]]}), {alternatives} := {carrier["theorem"]}']
            names.append(n)
        for j, evaluation in enumerate(model['evaluations']):
            declaration = statements[evaluation['statement_id']]['lean_declaration']
            args = ' '.join(f'({bindings[key]})' for key in evaluation['arguments'])
            proposition = f'@{declaration} {args}'
            if evaluation['value'] == 'violates':
                proposition = f'¬ ({proposition})'
            n = f'evaluation_{i}_{j}'
            lines += [f'theorem {n} : {proposition} := {evaluation["theorem"]}']
            names.append(n)
    lines += [f'#print axioms {n}' for n in names]
    lines += ['end FiniteModelCertificates']
    return '\n'.join(lines) + '\n', names


def verify_models(models, statements, root):
    if not models:
        return {'models': 0, 'certificates': 0, 'axioms': []}
    source, names = certificate_source(models, statements)
    with tempfile.NamedTemporaryFile('w', suffix='.lean', encoding='utf-8', delete=False, dir=root) as file:
        file.write(source)
        filename = file.name
    try:
        build = subprocess.run(['lake', 'build', *sorted({module for model in models for module in model['modules']})], cwd=root, text=True, capture_output=True, timeout=600)
        if build.returncode:
            raise ValueError(f'finite model modules failed to build:\n{build.stdout}\n{build.stderr}')
        result = subprocess.run(['lake', 'env', 'lean', filename], cwd=root, text=True, capture_output=True, timeout=600)
    except (OSError, subprocess.SubprocessError) as exc:
        raise ValueError(f'finite model verification unavailable: {exc}') from exc
    finally:
        Path(filename).unlink(missing_ok=True)
    if result.returncode:
        raise ValueError(f'finite model certificates failed:\n{result.stdout}\n{result.stderr}')
    for name in names:
        expected = f"'FiniteModelCertificates.{name}' does not depend on any axioms"
        if expected not in result.stdout:
            raise ValueError(f'certificate {name} is not zero-axiom: ' + '\n'.join(line for line in result.stdout.splitlines() if f"FiniteModelCertificates.{name}'" in line))
    return {'models': len(models), 'certificates': len(names), 'axioms': []}


def model_report(models, target=None, premises=()):
    """Unknown evaluations stay unknown; every requested premise must hold."""
    entries = []
    for model in sorted(models, key=lambda m: m['id']):
        values = {e['statement_id']: e['value'] for e in model['evaluations']}
        if target is not None and target not in values:
            continue
        missing = sorted(set(premises) - values.keys())
        failed = sorted(p for p in premises if values.get(p) == 'violates')
        qualifies = not missing and not failed
        entries.append({**model, 'target_value': values.get(target), 'missing_premises': missing,
                        'violated_premises': failed,
                        'classification': ('counterexample' if values.get(target) == 'violates' else 'satisfying_interpretation')
                        if qualifies and target else 'incomplete_or_inapplicable'})
    # Equal, nonempty failure sets across the same complete evaluation coverage.
    # Never compare vocabularies or treat absent evaluations as success.
    patterns = []
    for vocabulary in sorted({m['vocabulary'] for m in models}):
        group = [m for m in models if m['vocabulary'] == vocabulary]
        ids = sorted({e['statement_id'] for m in group for e in m['evaluations']})
        for a, b in combinations(ids, 2):
            evaluated = {m['id']: {e['statement_id']: e['value'] for e in m['evaluations']} for m in group}
            if not all(a in v and b in v for v in evaluated.values()):
                continue
            failures = [mid for mid, v in evaluated.items() if v[a] == 'violates']
            if failures and all((v[a] == 'violates') == (v[b] == 'violates') for v in evaluated.values()):
                patterns.append({'statement_ids': [a, b], 'vocabulary': vocabulary,
                                 'model_ids': sorted(evaluated), 'cofailure_model_ids': sorted(failures), 'status': 'candidate_only'})
    if target is not None:
        patterns = [pattern for pattern in patterns if target in pattern['statement_ids']]
    return {'target': target, 'premise_statement_ids': sorted(set(premises)), 'models': entries,
            'cofailure_candidates': patterns,
            'scope': 'Closed Lean applications in the registered finite vocabulary only; no metaphysical possibility, premise closure or entailment follows from registration.'}
