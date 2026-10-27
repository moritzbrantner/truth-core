"""Configuration inputs and live, fail-closed certificate composition.

No status is persisted here. Models remain in the finite-model registry and
inferences remain ordinary results. A profile supplies exact shared Lean
parameters, preventing a theorem about another frame/assignment from pruning.
"""
from __future__ import annotations

import re
from itertools import product
import subprocess
import tempfile
from pathlib import Path

from finite_models import NAME, TERM, verify_models

IDENTIFIER = re.compile(r'[A-Za-z_][A-Za-z_0-9]*\Z')
# Deliberately a small term language, not arbitrary Lean source in JSON.
TYPE = re.compile(r'(?:[A-Za-z_][A-Za-z_0-9.]*|→|\s)+\Z')


def validate_case(case, statements, results, arguments, models, root):
    allowed = {'id', 'description', 'seed_statement_id', 'semantics', 'configurations', 'incompatibility_result_ids', 'implication_result_ids', 'model_bindings'}
    if set(case) - allowed:
        raise ValueError('unknown configuration fields (derived statuses may not be stored)')
    if not isinstance(case.get('id'), str) or not re.fullmatch(r'CONFIG-[A-Z0-9-]+', case['id']):
        raise ValueError('configuration case needs a CONFIG- identifier')
    if not isinstance(case.get('seed_statement_id'), str) or case['seed_statement_id'] not in statements:
        raise ValueError('unknown configuration seed')
    profile = case.get('semantics')
    if not isinstance(profile, dict):
        raise ValueError('semantics must be an explicit object')
    if set(profile) - {'id', 'logic', 'frame', 'domain', 'identity', 'vocabulary', 'parameters', 'parameter_order', 'constants', 'applications', 'modules', 'permitted_axioms'}:
        raise ValueError('unknown semantics fields')
    for field in ('id', 'logic', 'frame', 'domain', 'identity', 'vocabulary'):
        if not isinstance(profile.get(field), str) or not profile[field].strip():
            raise ValueError(f'semantics requires {field}')
    axioms = profile.get('permitted_axioms')
    if not isinstance(axioms, list) or any(not isinstance(axiom, str) or axiom not in {'propext', 'Classical.choice', 'Quot.sound'} for axiom in axioms) or len(axioms) != len(set(axioms)):
        raise ValueError('profile requires explicit permitted_axioms from the approved axiom policy')
    parameters = profile.get('parameters')
    if not isinstance(parameters, list) or not parameters:
        raise ValueError('semantics requires ordered Lean parameters')
    names = []
    for parameter in parameters:
        if not isinstance(parameter, dict) or not isinstance(parameter.get('name'), str) or not IDENTIFIER.fullmatch(parameter['name']):
            raise ValueError('invalid parameter name')
        if not isinstance(parameter.get('type'), str) or not TYPE.fullmatch(parameter['type']):
            raise ValueError('invalid parameter type (only names, application and arrows accepted)')
        names.append(parameter['name'])
    if len(names) != len(set(names)):
        raise ValueError('duplicate profile parameter')
    constants = profile.get('constants', {})
    if not isinstance(constants, dict) or any(not isinstance(name, str) or not IDENTIFIER.fullmatch(name) or name in names or not isinstance(term, str) or not TERM.fullmatch(term) for name, term in constants.items()):
        raise ValueError('invalid/overlapping fixed profile constants')
    names += list(constants)
    order = profile.get('parameter_order', names)
    if not isinstance(order, list) or any(not isinstance(name, str) for name in order) or len(order) != len(set(order)) or set(order) != set(names):
        raise ValueError('parameter_order must list every variable and fixed role exactly once')
    # Supported role shapes (all non-propositional, so no proof can hide in a
    # parameter): a carrier `Type`, a fixed carrier constant (Bool or Nat), a
    # Kripke frame on a carrier, an element of a carrier, and a predicate or
    # relation `X₁ → … → Xₙ → Prop` over carriers. Carriers must be declared
    # before they are used. The necessary-individual profiles (W, I, F,
    # present, w) are one instance; the Megarian capacity profile (#576) is
    # another.
    if any(term not in {'Bool', 'Nat'} for term in constants.values()):
        raise ValueError('supported fixed carriers are Bool or Nat; proposition-valued carriers are forbidden')
    # A fixed carrier is referred to by its term (`Bool`), never by its role name.
    carriers = set(constants.values())
    for parameter in parameters:
        kind = ' '.join(parameter['type'].split())
        words = kind.split(' → ')
        if kind == 'Type':
            carriers.add(parameter['name'])
        elif kind.startswith('TruthCore.Modal.Frame ') and kind.split(' ', 1)[1] in carriers:
            pass
        elif kind in carriers:
            pass
        elif len(words) >= 2 and words[-1] == 'Prop' and all(word in carriers for word in words[:-1]):
            pass
        else:
            raise ValueError(f"{parameter['name']}: unsupported semantic role type; proof-valued parameters are forbidden")
    applications = profile.get('applications')
    if not isinstance(applications, dict) or not applications:
        raise ValueError('profile requires explicit statement applications')
    for sid, args in applications.items():
        if sid not in statements or not isinstance(statements[sid].get('lean_declaration'), str) or not NAME.fullmatch(statements[sid]['lean_declaration']):
            raise ValueError(f'unknown/unbound statement {sid}')
        if not isinstance(args, list) or any(not isinstance(arg, str) or arg not in names for arg in args):
            raise ValueError(f'{sid}: arguments must reference profile parameters')
    selections = case.get('configurations')
    if not isinstance(selections, list) or not selections:
        raise ValueError('case requires named configurations')
    seen = set()
    for selection in selections:
        if not isinstance(selection, dict) or not isinstance(selection.get('id'), str) or not re.fullmatch(r'[a-z][a-z0-9-]*', selection['id']) or selection['id'] in seen:
            raise ValueError('invalid/duplicate selection id')
        seen.add(selection['id'])
        if set(selection) != {'id', 'statement_ids'}:
            raise ValueError('selection stores only its id and statement set')
        ids = selection.get('statement_ids')
        if not isinstance(ids, list) or any(not isinstance(sid, str) or sid not in applications for sid in ids) or len(ids) != len(set(ids)):
            raise ValueError('selection needs unique profile statement IDs')
    for field in ('incompatibility_result_ids', 'implication_result_ids'):
        ids = case.get(field, [])
        if not isinstance(ids, list) or any(not isinstance(rid, str) or rid not in results for rid in ids) or len(ids) != len(set(ids)):
            raise ValueError(f'{field} must reference unique existing results')
        for rid in ids:
            result = results[rid]
            if any(not isinstance(result.get(key), str) or not NAME.fullmatch(result[key]) for key in ('theorem', 'solution_module')):
                raise ValueError(f'{rid}: invalid result declarations')
            if field == 'implication_result_ids' and result.get('transcription'):
                raise ValueError(f'{rid}: transcription cannot supply a configuration deduction')
            argument = arguments.get(result['argument_id'])
            if not argument or any(sid not in applications for sid in argument['premise_statement_ids']):
                raise ValueError(f'{rid}: all premises require profile applications')
            if field == 'implication_result_ids' and statements.get(argument['conclusion_statement_id'], {}).get('lean_declaration') == 'TruthCore.Logic.ConfigurationFalse':
                raise ValueError(f'{rid}: False-concluding results belong in incompatibility_result_ids, not implication rules')
            if field == 'implication_result_ids' and argument['conclusion_statement_id'] not in applications:
                raise ValueError(f'{rid}: conclusion requires profile application')
    if set(case.get('incompatibility_result_ids', [])) & set(case.get('implication_result_ids', [])):
        raise ValueError('a contradiction certificate cannot also be an implication rule')
    witnesses = case.get('model_bindings', [])
    if not isinstance(witnesses, list):
        raise ValueError('model_bindings must be a list')
    seen = set()
    for witness in witnesses:
        mid = witness.get('model_id') if isinstance(witness, dict) else None
        if not isinstance(mid, str) or mid not in models or mid in seen:
            raise ValueError('unknown/duplicate configuration model')
        seen.add(mid)
        model = models[mid]
        if model['vocabulary'] != profile['vocabulary']:
            raise ValueError(f'{mid}: vocabulary/profile mismatch')
        bindings = witness.get('parameters')
        if not isinstance(bindings, dict) or set(bindings) != set(names) or any(not isinstance(key, str) or key not in model['bindings'] for key in bindings.values()):
            raise ValueError(f'{mid}: complete profile-to-model parameter binding required')
        for evaluation in model['evaluations']:
            sid = evaluation['statement_id']
            if sid in applications and evaluation['arguments'] != [bindings[arg] for arg in applications[sid]]:
                raise ValueError(f'{mid}/{sid}: evaluation does not use the same profile assignment')
    omitted = {mid for mid, model in models.items() if model['vocabulary'] == profile['vocabulary']} - seen
    if omitted:
        raise ValueError(f'profile omits registered models in its vocabulary: {sorted(omitted)}')
    modules = profile.get('modules')
    if not isinstance(modules, list) or not modules or len(modules) != len(set(modules)) or any(not isinstance(m, str) or not NAME.fullmatch(m) or not (root / (m.replace('.', '/') + '.lean')).is_file() for m in modules):
        raise ValueError('semantics modules must name existing unique Lean modules')


def application(profile, statements, sid):
    args = ' '.join(profile.get('constants', {}).get(role, role) for role in profile['applications'][sid])
    return f'(@{statements[sid]["lean_declaration"]} {args})'


def model_profile_mismatches(case, registration, models):
    model = models[registration['model_id']]
    return [{'parameter': role, 'expected': term, 'registered': model['bindings'][registration['parameters'][role]]}
            for role, term in sorted(case['semantics'].get('constants', {}).items())
            if model['bindings'][registration['parameters'][role]] != term]


def generated_names(source):
    return re.findall(r'^(?:theorem|def) ([A-Za-z_][A-Za-z_0-9]*)', source, re.MULTILINE)


def check_generated_axioms(output, source, namespace, permitted):
    for name in generated_names(source):
        qualified = namespace + '.' + name
        if f"'{qualified}' does not depend on any axioms" in output:
            continue
        match = re.search(re.escape(f"'{qualified}' depends on axioms:") + r'\s*\[([^\]]*)\]', output)
        if not match:
            raise ValueError(f'missing axiom verification for {qualified}')
        actual = {axiom.strip() for axiom in match[1].split(',') if axiom.strip()}
        if not actual <= set(permitted):
            raise ValueError(f'{qualified}: profile-forbidden axioms {sorted(actual - set(permitted))}')


def certificate_source(case, statements, results, arguments, models=None):
    profile = case['semantics']
    models = models or {}
    eligible = [entry for entry in case.get('model_bindings', []) if entry['model_id'] in models and not model_profile_mismatches(case, entry, models)]
    modules = set(profile['modules']) | {results[rid]['solution_module'] for rid in case.get('incompatibility_result_ids', []) + case.get('implication_result_ids', [])}
    modules |= {module for entry in eligible for module in models[entry['model_id']]['modules']}
    lines = [f'import {module}' for module in sorted(modules)]
    lines.append('namespace ConfigurationCertificates')
    parameters = ' '.join(f'({p["name"]} : {p["type"]})' for p in profile['parameters'])
    variable_names = [p['name'] for p in profile['parameters']]
    order = profile.get('parameter_order', variable_names)
    constants = profile.get('constants', {})
    for index, rid in enumerate(case.get('incompatibility_result_ids', []) + case.get('implication_result_ids', [])):
        result = results[rid]
        argument = arguments[result['argument_id']]
        hypotheses = [application(profile, statements, sid) for sid in argument['premise_statement_ids']]
        conclusion = 'False' if rid in case.get('incompatibility_result_ids', []) else application(profile, statements, argument['conclusion_statement_id'])
        expected = ' → '.join(hypotheses + [conclusion])
        # Explicitly specialize the original theorem at fixed profile roles.
        theorem_args = ' '.join(constants.get(role, role) for role in order)
        lines.append(f'theorem certificate_{index} : ∀ {parameters}, {expected} := by')
        lines.append('  intro ' + ' '.join(variable_names))
        lines.append(f'  exact @{result["theorem"]} {theorem_args}')
    for index, entry in enumerate(eligible):
        model = models[entry['model_id']]
        substitutions = {role: model['bindings'][key] for role, key in entry['parameters'].items()}
        for j, parameter in enumerate(profile['parameters']):
            expected = parameter['type']
            expected = re.sub(r'\b[A-Za-z_][A-Za-z_0-9]*\b', lambda match: '(' + substitutions[match[0]] + ')' if match[0] in substitutions else match[0], expected)
            lines.append(f'def model_parameter_{index}_{j} : {expected} := {substitutions[parameter["name"]]}')
    lines += [f'#print axioms {name}' for name in generated_names('\n'.join(lines))]
    lines.append('end ConfigurationCertificates')
    return '\n'.join(lines) + '\n'


def verify_case(case, statements, results, arguments, models, root, verified_results=None):
    """Rebuild first; no marker, stale olean or result registration is success."""
    selected = case.get('incompatibility_result_ids', []) + case.get('implication_result_ids', [])
    witnesses = [models[item['model_id']] for item in case.get('model_bindings', []) if not model_profile_mismatches(case, item, models)]
    modules = sorted(set(case['semantics']['modules']) | {results[rid]['solution_module'] for rid in selected} | {module for model in witnesses for module in model['modules']})
    def run(command):
        try:
            result = subprocess.run(command, cwd=root, text=True, capture_output=True, timeout=1200)
        except (OSError, subprocess.SubprocessError) as exc:
            raise ValueError(f'configuration verification unavailable: {exc}') from exc
        if result.returncode:
            raise ValueError(f'configuration verification failed ({command}):\n{result.stdout}\n{result.stderr}')
        return result
    run(['lake', 'build', *modules])
    source = certificate_source(case, statements, results, arguments, models)
    with tempfile.NamedTemporaryFile('w', suffix='.lean', encoding='utf-8', delete=False, dir=root) as file:
        file.write(source)
        filename = Path(file.name)
    try:
        result = run(['lake', 'env', 'lean', str(filename)])
        check_generated_axioms(result.stdout, source, 'ConfigurationCertificates', case['semantics']['permitted_axioms'])
    finally:
        filename.unlink(missing_ok=True)
    if verified_results is None:
        verified_results = set()
    reused = sorted(set(selected) & verified_results)
    for rid in sorted(set(selected) - verified_results):
        run(['scripts/verify-result.sh', rid])
        verified_results.add(rid)
    model_verification = verify_models(witnesses, statements, root)
    return {'result_ids': sorted(set(selected)), 'reused_result_ids_in_this_invocation': reused, 'models': model_verification}


def configuration_report(case, results, arguments, models, *, verified=False, selection=None):
    """Prune by cores and verified implication supports; no powerset search."""
    def witnesses_for(assumptions):
        found = []
        for registration in case.get('model_bindings', []):
            if model_profile_mismatches(case, registration, models):
                continue
            model = models[registration['model_id']]
            values = {item['statement_id']: item['value'] for item in model['evaluations']}
            if all(values.get(sid) == 'satisfies' for sid in assumptions):
                found.append(model['id'])
        return sorted(found)
    entries = []
    selections = [selection] if selection is not None else case['configurations']
    for choice in sorted(selections, key=lambda item: item['id']):
        assumptions = set(choice['statement_ids'])
        closure = implication_closure(assumptions, case, results, arguments, include_assumptions=True) if verified else None
        supports = ({item['statement_id']: item['sufficient_subsets'] for item in closure['items']} if closure else
                    {sid: [{'statement_ids': [sid], 'result_ids': []}] for sid in assumptions})
        candidates = []
        work = 0
        truncated = False
        for rid in sorted(case.get('incompatibility_result_ids', [])):
            argument = arguments[results[rid]['argument_id']]
            premises = argument['premise_statement_ids']
            if any(sid not in supports for sid in premises):
                continue
            for chosen in product(*(supports[sid] for sid in premises)):
                work += 1
                if work > 128:
                    truncated = True
                    break
                subset = sorted({sid for item in chosen for sid in item['statement_ids']})
                chain = list(dict.fromkeys([result for item in chosen for result in item['result_ids']] + [rid]))
                candidates.append({'statement_ids': subset, 'certificate_statement_ids': sorted(premises),
                                   'result_id': rid, 'argument_id': argument['id'], 'theorem': results[rid]['theorem'],
                                   'result_ids': chain, 'theorems': [results[result]['theorem'] for result in chain]})
            if truncated:
                break
        unique = {}
        for core in candidates:
            unique.setdefault(tuple(core['statement_ids']), core)
        matching = [core for core in unique.values() if not any(set(other['statement_ids']) < set(core['statement_ids']) for other in unique.values())]
        matching.sort(key=lambda core: (len(core['statement_ids']), core['statement_ids'], core['result_id']))
        for core in matching:
            removal = [{'removed_statement_id': sid, 'model_ids': witnesses_for(set(core['statement_ids']) - {sid})}
                       for sid in core['statement_ids']]
            core['removal_evidence'] = removal
            core['minimality'] = ('inclusion-minimal (each single removal has a certified model)'
                                  if verified and all(item['model_ids'] for item in removal)
                                  else 'minimal among found certificate compositions (bounded search); proper-subset compatibility unresolved by available witnesses'
                                  if truncated or bool(closure and closure['truncated'])
                                  else 'minimal among supplied incompatibility certificates; proper-subset compatibility unresolved by available witnesses')
        witnesses = witnesses_for(assumptions)
        if verified and matching and witnesses:
            raise ValueError('verification defect: incompatible core overlaps a model under the same semantics')
        status = ('verified incompatible' if matching else 'model witnessed' if witnesses else 'unresolved') if verified else 'verification required'
        consequences = None
        if verified and not matching:
            consequences = {**closure, 'items': [item for item in closure['items'] if item['statement_id'] not in assumptions]}
        entries.append({'id': choice['id'], 'statement_ids': sorted(assumptions), 'status': status,
                        'incompatible_cores': matching, 'model_ids': witnesses,
                        'model_witnesses': [{'model_id': mid, 'lean_declaration': models[mid]['lean_declaration'],
                                             'evaluations': [evaluation for evaluation in models[mid]['evaluations'] if evaluation['statement_id'] in assumptions]} for mid in witnesses],
                        'unresolved_reason': ('No certified core found within the reported search bound and no applicable registered model covers the complete selection.'
                                              if truncated or bool(closure and closure['truncated'])
                                              else 'No applicable certified core or registered model covers the complete selection in this profile.') if status == 'unresolved' else None,
                        'consequences': consequences,
                        'core_composition': {'combinations_checked': min(work, 128), 'limit': 128, 'truncated': truncated or bool(closure and closure['truncated'])}})
    return {'id': case['id'], 'seed_statement_id': case['seed_statement_id'], 'semantics': case['semantics'],
            'verified': verified, 'configurations': entries,
            'inapplicable_models': [{'model_id': item['model_id'], 'profile_mismatches': model_profile_mismatches(case, item, models)} for item in case.get('model_bindings', []) if model_profile_mismatches(case, item, models)],
            'scope': 'Formal encoding and registered model class only; no metaphysical possibility or premise closure follows. Unresolved means unresolved by available certified artifacts, not logical undecidability. Conditional proved/closed labels are never imported as premise-free facts; only selected assumptions and exact verified theorem hypotheses enter composition.'}


def implication_closure(assumptions, case, results, arguments, limit=128, include_assumptions=False):
    """Keep an antichain of sufficient supports; deterministic and explicitly bounded.

    Assumptions are supplied, not independently enumerated. Each proof support is
    composed only from named, verified rules. Cycles cannot introduce a premise.
    """
    supports = {sid: {frozenset([sid]): ()} for sid in sorted(assumptions)}
    rules = [(rid, arguments[results[rid]['argument_id']]) for rid in sorted(case.get('implication_result_ids', []))]
    work = 0
    truncated = False
    changed = True
    while changed and not truncated:
        changed = False
        for rid, argument in rules:
            premises = argument['premise_statement_ids']
            if any(not supports.get(sid) for sid in premises):
                continue
            options = [list(supports[sid].items()) for sid in premises]
            for chosen in product(*options):
                work += 1
                if work > limit:
                    truncated = True
                    break
                support = frozenset().union(*(item[0] for item in chosen))
                chain = tuple(dict.fromkeys([result for item in chosen for result in item[1]] + [rid]))
                bucket = supports.setdefault(argument['conclusion_statement_id'], {})
                if any(existing <= support for existing in bucket):
                    continue
                for existing in list(bucket):
                    if support < existing:
                        del bucket[existing]
                bucket[support] = chain
                changed = True
            if truncated:
                break
    return {'items': [{'statement_id': sid,
                       'sufficient_subsets': [{'statement_ids': sorted(subset), 'result_ids': list(chain),
                                               'theorems': [results[rid]['theorem'] for rid in chain]}
                                              for subset, chain in sorted(bucket.items(), key=lambda item: (len(item[0]), sorted(item[0])))],
                       'minimality': 'minimal among found supports' if truncated else 'inclusion-minimal for supplied verified rules'}
                      for sid, bucket in sorted(supports.items()) if include_assumptions or sid not in assumptions],
            'limit': limit, 'combinations_checked': min(work, limit), 'truncated': truncated}


def composition_source(case, report, statements, results, arguments):
    """Replay each reported composed core as a Lean proof term over its inputs."""
    profile = case['semantics']
    modules = set(profile['modules']) | {results[rid]['solution_module'] for rid in case.get('incompatibility_result_ids', []) + case.get('implication_result_ids', [])}
    lines = [f'import {module}' for module in sorted(modules)]
    lines.append('namespace ConfigurationCompositions')
    parameters = ' '.join(f'({p["name"]} : {p["type"]})' for p in profile['parameters'])
    names = [p['name'] for p in profile['parameters']]
    role_args = ' '.join(profile.get('constants', {}).get(role, role) for role in profile.get('parameter_order', names))
    count = 0
    for entry in report['configurations']:
        for core in entry['incompatible_cores']:
            assumptions = core['statement_ids']
            expected = ' → '.join([application(profile, statements, sid) for sid in assumptions] + ['False'])
            hypothesis = {sid: f'h_{i}' for i, sid in enumerate(assumptions)}
            lines.append(f'theorem composition_{count} : ∀ {parameters}, {expected} := by')
            lines.append('  intro ' + ' '.join(names + list(hypothesis.values())))
            for index, rid in enumerate(core['result_ids']):
                argument = arguments[results[rid]['argument_id']]
                premise_args = ' '.join(hypothesis[sid] for sid in argument['premise_statement_ids'])
                term = f'@{results[rid]["theorem"]} {role_args} {premise_args}'
                if rid == core['result_id']:
                    lines.append(f'  exact {term}')
                else:
                    sid = argument['conclusion_statement_id']
                    name = f'derived_{index}'
                    lines.append(f'  have {name} : {application(profile, statements, sid)} := {term}')
                    hypothesis[sid] = name
            count += 1
    lines += [f'#print axioms {name}' for name in generated_names('\n'.join(lines))]
    lines.append('end ConfigurationCompositions')
    return '\n'.join(lines) + '\n', count


def verify_compositions(case, report, statements, results, arguments, root):
    source, count = composition_source(case, report, statements, results, arguments)
    if not count:
        return {'cores': 0}
    with tempfile.NamedTemporaryFile('w', suffix='.lean', encoding='utf-8', delete=False, dir=root) as file:
        file.write(source)
        filename = Path(file.name)
    try:
        result = subprocess.run(['lake', 'env', 'lean', str(filename)], cwd=root, text=True, capture_output=True, timeout=600)
        if result.returncode:
            raise ValueError(f'configuration composition rejected:\n{result.stdout}\n{result.stderr}')
        check_generated_axioms(result.stdout, source, 'ConfigurationCompositions', case['semantics']['permitted_axioms'])
    except (OSError, subprocess.SubprocessError) as exc:
        raise ValueError(f'configuration composition verification unavailable: {exc}') from exc
    finally:
        filename.unlink(missing_ok=True)
    return {'cores': count}
