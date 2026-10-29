"""Check the coverage/freshness of one reviewed bundle, never semantic truth."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
AUDIT = ROOT / 'docs/notes/classical-attributes-migration.json'
AUDITS = (AUDIT, ROOT / 'docs/notes/classical-attributes-all-migration.json')


def records(root):
    return {kind: {data['id']: (path, data)
                   for path in (root / 'corpus' / kind).glob('*.json')
                   if 'id' in (data := json.loads(path.read_text()))}
            for kind in ('arguments', 'results', 'statements', 'inferences',
                         'definitions', 'disambiguations', 'claims')}


def expected_scope(index, result_id):
    result = index['results'][result_id][1]
    argument = index['arguments'][result['argument_id']][1]
    statements = set(argument['premise_statement_ids'] + [argument['conclusion_statement_id']])
    for iid in argument['inference_ids']:
        step = index['inferences'][iid][1]
        statements.update(step['input_statement_ids'])
        statements.add(step['output_statement_id'])
    owners = [argument] + [index['statements'][sid][1] for sid in statements]
    return {
        'results': {result_id}, 'arguments': {argument['id']}, 'statements': statements,
        'inferences': set(argument['inference_ids']),
        'definitions': {did for owner in owners for did in owner.get('definition_ids', [])} | {'DEF-PURE-ACT'},
        'disambiguations': {did for owner in owners for did in owner.get('disambiguation_ids', [])},
        # Only this source interpretation is clarified. Other source claims are
        # retained evidence, not silently declared freshly audited.
        'claims': {'VATICAN-I-DEI-FILIUS-CH1-ONE-TRUE-LIVING-GOD'},
    }


def check(root=ROOT, audit=None):
    audit = audit if audit is not None else json.loads(AUDIT.read_text())
    from expression_contracts import contracts
    contract = contracts().get(audit['result_id'])
    if contract is None or contract['baseline_revision'] != audit['base_head']:
        raise ValueError('missing reviewed expression contract for the audited result')
    index = records(root)
    expected = expected_scope(index, audit['result_id'])
    for rid in audit.get('consumer_result_ids', []):
        related = contracts().get(rid)
        if related is None or related['baseline_revision'] != audit['base_head']:
            raise ValueError('missing reviewed expression contract for a scoped consumer')
        for kind, ids in expected_scope(index, rid).items():
            expected[kind].update(ids)
    actual = {kind: set() for kind in expected}
    for row in audit['records']:
        kind, rid = row['kind'], row['id']
        if kind not in actual or rid in actual[kind]:
            raise ValueError(f'duplicate or unknown audit kind: {kind}/{rid}')
        actual[kind].add(rid)
        path, _ = index[kind][rid]
        if row['path'] != str(path.relative_to(root)):
            raise ValueError(f'audit path mismatch: {rid}')
        if hashlib.sha256(path.read_bytes()).hexdigest() != row['reviewed_sha256']:
            raise ValueError(f'audit requires review after record change: {rid}')
        if row['status'] not in ('inspected', 'repaired', 'unresolved') or not row['finding'].strip():
            raise ValueError(f'missing audit disposition: {rid}')
        if not row.get('before', {}).get('sha256') or not row.get('classification'):
            raise ValueError(f'missing before-state or classification: {rid}')
    if actual != expected:
        raise ValueError('audit coverage differs from the selected argument and its inference/term closure')
    return audit


if __name__ == '__main__':
    for path in AUDITS:
        checked = check(audit=json.loads(path.read_text()))
        print(f"{checked['result_id']}: {len(checked['records'])} exact record dispositions; semantic adequacy remains reviewed")
