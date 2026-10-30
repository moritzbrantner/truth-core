"""Disposable verified explorer outputs; never inputs to proof or frontier gates.

Freshness checks bind a trusted producer's output to the current source inputs.
They do not execute Lean again or turn a digest into proof verification.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import subprocess
import tempfile

from configurations import configuration_report, model_profile_mismatches, verify_compositions

SCHEMA_VERSION = 1
# Bound exhaustive transport generation to at most 1,024 syntactic selections.
# The Night case has nine dimensions, including derived conclusions and controls.
MAX_DIMENSIONS = 10
PRODUCER_TRUST = "Output of the trusted verification producer. Digest validation checks freshness, not fresh proof execution."
INPUT_FILES = (
    'lean-toolchain', 'lakefile.toml', 'lake-manifest.json', 'TruthCore.lean',
    'scripts/corpus.py', 'scripts/configurations.py', 'scripts/configuration_explorer.py',
    'scripts/finite_models.py', 'scripts/premise_dossiers.py', 'scripts/source_evidence.py',
    'scripts/BindTypes.lean', 'scripts/verify-result.sh', 'scripts/verifier-pins.env',
    'scripts/bootstrap-verifier.sh', 'verifier/Cargo.toml', 'verifier/Cargo.lock',
)
INPUT_DIRECTORIES = (
    ('TruthCore', '*.lean'), ('results', 'comparator.json'), ('verifier/src', '*.rs'),
    ('corpus/statements', '*.json'), ('corpus/arguments', '*.json'),
    ('corpus/results', '*.json'),
    ('corpus/models', '*.json'), ('corpus/configurations', '*.json'),
)


def input_manifest(root):
    """Cover the existing global transcription scan and exact configuration inputs; exclude docs/CSS."""
    paths = {root / path for path in INPUT_FILES}
    for directory, pattern in INPUT_DIRECTORIES:
        paths.update((root / directory).rglob(pattern))
    manifest = {}
    for path in sorted(paths):
        if path.is_symlink() or not path.is_file():
            raise ValueError(f'configuration report input is missing or a symlink: {path.relative_to(root)}')
        manifest[path.relative_to(root).as_posix()] = hashlib.sha256(path.read_bytes()).hexdigest()
    return manifest


def input_digest(manifest):
    encoded = json.dumps(manifest, sort_keys=True, separators=(',', ':')).encode('utf-8')
    return hashlib.sha256(encoded).hexdigest()


def source_head(root):
    try:
        result = subprocess.run(['git', 'rev-parse', 'HEAD'], cwd=root, text=True, capture_output=True, timeout=10)
    except (OSError, subprocess.SubprocessError) as exc:
        raise ValueError(f'cannot resolve producer source head: {exc}') from exc
    if result.returncode:
        raise ValueError('cannot resolve producer source head: ' + result.stderr.strip())
    return result.stdout.strip()


def bounded_family(case, classify):
    """Emit a decision tree, pruning whole families with cores and shared witnesses.

    The browser only follows edges. It does not implement consistency, implication
    closure or a new proof-status engine. Counts concern syntactic selections.
    """
    dimensions = sorted(case['semantics']['applications'])
    if len(dimensions) > MAX_DIMENSIONS:
        raise ValueError(f'{case["id"]}: explorer supports at most {MAX_DIMENSIONS} assumption dimensions')
    nodes = []
    memo = {}
    def report_for(ids):
        key = tuple(sorted(ids))
        if key not in memo:
            memo[key] = classify(list(key))
        return memo[key]
    def visit(selected, index):
        remaining = dimensions[index:]
        prefix = report_for(selected)
        full = report_for(selected + remaining)
        terminal = None
        if prefix['status'] == 'verified incompatible':
            terminal = prefix
        elif full['status'] == 'model witnessed':
            # This one certified assignment covers every member of the family.
            terminal = full
        elif (not prefix['model_ids'] and full['status'] == 'unresolved'
              and not full['core_composition']['truncated']):
            # No registered model covers the prefix, so none covers a superset;
            # a complete supplied-rule closure has no core even at the extension.
            terminal = prefix
        elif not remaining:
            terminal = prefix
        identifier = f'n{len(nodes)}'
        node = {'id': identifier}
        nodes.append(node)
        if terminal is not None:
            node.update(kind='terminal', required_statement_ids=list(selected), optional_statement_ids=remaining,
                        report=terminal, syntactic_selections_covered=2 ** len(remaining))
        else:
            node.update(kind='decision', statement_id=remaining[0],
                        exclude=visit(selected, index + 1), include=visit(selected + [remaining[0]], index + 1))
        return identifier
    root_node = visit([], 0)
    terminals = [node for node in nodes if node['kind'] == 'terminal']
    return {'statement_ids': dimensions, 'max_dimensions': MAX_DIMENSIONS, 'root': root_node, 'nodes': nodes,
            'limits': {'classifier_calls': len(memo), 'decision_nodes': len(nodes) - len(terminals),
                       'terminal_families': len(terminals), 'syntactic_selections': 2 ** len(dimensions),
                       'covered_selections': sum(node['syntactic_selections_covered'] for node in terminals),
                       'note': 'Counts describe bounded syntactic assumption selections, not philosophically distinct theories. Incomplete implication/core closure remains explicit in terminal reports.'}}


def build_case_spaces(context, reports, *, root=None):
    """The caller supplies freshly verified reports; optional root replays family cores."""
    by_id = {report['id']: report for report in reports}
    cases = []
    for case in context['cases']:
        report = by_id[case['id']]
        if report['verified'] is not True or not isinstance(report.get('verification'), dict):
            raise ValueError('registered or unverified data cannot produce a certified explorer bundle')
        def classify(ids):
            return configuration_report(case, context['results'], context['arguments'], context['models'],
                                        verified=True, selection={'id': 'selection', 'statement_ids': ids})['configurations'][0]
        space = bounded_family(case, classify)
        if root is not None:
            terminals = [node['report'] for node in space['nodes'] if node['kind'] == 'terminal']
            verification = verify_compositions(case, {'configurations': terminals}, context['statements'],
                                               context['results'], context['arguments'], root)
        else:
            verification = None
        implications = [{'result_id': rid, 'theorem': context['results'][rid]['theorem'],
                         'premise_statement_ids': context['arguments'][context['results'][rid]['argument_id']]['premise_statement_ids'],
                         'conclusion_statement_id': context['arguments'][context['results'][rid]['argument_id']]['conclusion_statement_id']}
                        for rid in sorted(case.get('implication_result_ids', []))]
        cases.append({**report, 'assumption_space': space, 'verified_implications': implications, 'family_verification': verification})
    return cases


def write_bundle(root, output, context, reports, initial_manifest):
    """Verify new family proofs, then atomically replace one ignored output file."""
    if output.is_symlink() or (root / '.cache').is_symlink():
        raise ValueError('configuration output/cache symlinks are unsupported')
    output = output.resolve()
    cache = (root / '.cache').resolve()
    if not output.is_relative_to(cache):
        raise ValueError('configuration report output must be inside the clone .cache directory')
    cases = build_case_spaces(context, reports, root=root)
    final_manifest = input_manifest(root)
    if initial_manifest != final_manifest:
        raise ValueError('configuration inputs changed during report verification; discard and rerun')
    bundle = {'schema_version': SCHEMA_VERSION,
              'producer': {'mode': 'live-verified', 'source_head': source_head(root),
                           'input_digest': input_digest(final_manifest), 'inputs': final_manifest,
                           'trust': PRODUCER_TRUST},
              'cases': cases}
    output.parent.mkdir(parents=True, exist_ok=True)
    temporary = None
    try:
        with tempfile.NamedTemporaryFile('w', encoding='utf-8', dir=output.parent, delete=False) as file:
            temporary = Path(file.name)
            json.dump(bundle, file, ensure_ascii=False, sort_keys=True, indent=2)
            file.write('\n')
        temporary.replace(output)
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)
    return bundle


def read_bundle(root, path, context):
    """Validate trusted output freshness/projection; this is NOT a fresh proof gate."""
    if path.is_symlink() or (root / '.cache').is_symlink():
        raise ValueError('configuration report/cache symlinks are unsupported')
    try:
        bundle = json.loads(path.read_text(encoding='utf-8'))
    except (OSError, json.JSONDecodeError) as exc:
        raise ValueError(f'cannot read configuration report: {exc}') from exc
    if not isinstance(bundle, dict) or type(bundle.get('schema_version')) is not int or bundle['schema_version'] != SCHEMA_VERSION:
        raise ValueError('unsupported configuration report schema')
    producer = bundle.get('producer')
    if not isinstance(producer, dict) or producer.get('mode') != 'live-verified' or producer.get('trust') != PRODUCER_TRUST:
        raise ValueError('configuration report lacks a live-verification producer')
    manifest = input_manifest(root)
    if (producer.get('source_head') != source_head(root) or producer.get('inputs') != manifest
            or producer.get('input_digest') != input_digest(manifest)):
        raise ValueError('stale configuration report: source head or current input digest differs')
    reports = bundle.get('cases')
    if not isinstance(reports, list) or len(reports) != len(context['cases']):
        raise ValueError('configuration report does not cover the exact current cases')
    expected_reports = []
    for case, report in zip(context['cases'], reports):
        if not isinstance(report, dict) or report.get('verified') is not True:
            raise ValueError('malformed configuration report case')
        expected = configuration_report(case, context['results'], context['arguments'], context['models'], verified=True)
        for key, value in expected.items():
            if json.dumps(report.get(key), sort_keys=True) != json.dumps(value, sort_keys=True):
                raise ValueError(f'{case["id"]}: configuration projection disagrees with current inputs')
        verification = report.get('verification')
        selected = sorted(set(case.get('incompatibility_result_ids', []) + case.get('implication_result_ids', [])))
        if (not isinstance(verification, dict) or verification.get('result_ids') != selected
                or verification.get('original_bound_result_ids') != selected):
            raise ValueError(f'{case["id"]}: missing exact original theorem verification provenance')
        eligible = [context['models'][entry['model_id']] for entry in case.get('model_bindings', []) if not model_profile_mismatches(case, entry, context['models'])]
        model_gate = {'models': len(eligible), 'certificates': sum(1 + len(model['carriers']) + len(model['evaluations']) for model in eligible), 'axioms': []}
        named_cores = sum(len(entry['incompatible_cores']) for entry in expected['configurations'])
        if verification.get('models') != model_gate or verification.get('compositions') != {'cores': named_cores}:
            raise ValueError(f'{case["id"]}: missing exact model/composition verification provenance')
        expected_reports.append({**expected, 'verification': verification})
    expected_spaces = build_case_spaces(context, expected_reports)
    for actual, expected in zip(reports, expected_spaces):
        if actual.get('verified_implications') != expected['verified_implications']:
            raise ValueError('conditional theorem provenance disagrees with current inputs')
        if actual.get('assumption_space') != expected['assumption_space']:
            raise ValueError('configuration decision tree disagrees with canonical projection')
        count = sum(len(node['report']['incompatible_cores']) for node in expected['assumption_space']['nodes'] if node['kind'] == 'terminal')
        if actual.get('family_verification') != {'cores': count}:
            raise ValueError('missing exact family-core verification provenance')
    return bundle
