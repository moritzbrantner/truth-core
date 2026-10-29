"""Disposable corpus lookup index. Registration is never proof certification."""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import math
from collections import Counter
from pathlib import Path
import sqlite3
import tempfile

ROOT = Path(__file__).resolve().parents[1]
SCHEMA = '3'


def inputs(root):
    return sorted((root / 'corpus').rglob('*.json'))


def digest(root):
    h = hashlib.sha256()
    for path in inputs(root):
        h.update(path.relative_to(root).as_posix().encode())
        h.update(b'\0')
        h.update(path.read_bytes())
        h.update(b'\0')
    h.update(Path(__file__).read_bytes())
    return h.hexdigest()


def references(value):
    if isinstance(value, str):
        yield value
    elif isinstance(value, list):
        for item in value:
            yield from references(item)
    elif isinstance(value, dict):
        for item in value.values():
            yield from references(item)


def entities(path, value):
    """Project entities without flattening away a passage's shared witness."""
    if isinstance(value, dict) and isinstance(value.get('id'), str):
        yield path.parent.name, value
    if path.parent.name == 'passages' and isinstance(value, dict):
        for passage in value.get('passages', []):
            if not isinstance(passage, dict) or not isinstance(passage.get('id'), str):
                raise ValueError(f'invalid nested passage in {path}')
            yield 'passages', {'id': passage['id'], 'passage': passage,
                               'snapshot': value.get('snapshot'), 'collection_notes': value.get('notes')}


def build(root, destination):
    """Build atomically, refusing mixed snapshots or duplicate record identities."""
    before = digest(root)
    destination.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(dir=destination.parent, suffix='.sqlite', delete=False) as file:
        temporary = Path(file.name)
    try:
        db = sqlite3.connect(temporary)
        try:
            db.executescript('''
                CREATE TABLE metadata(key TEXT PRIMARY KEY, value TEXT NOT NULL);
                CREATE TABLE source_files(path TEXT PRIMARY KEY, content BLOB NOT NULL);
                CREATE TABLE records(key TEXT PRIMARY KEY, id TEXT, kind TEXT, path TEXT, body TEXT);
                CREATE INDEX records_id ON records(id);
                CREATE TABLE refs(owner TEXT, target TEXT, PRIMARY KEY(owner,target));
                CREATE INDEX refs_target ON refs(target);
                CREATE TABLE arguments(id TEXT PRIMARY KEY, signature TEXT, conclusion TEXT);
                CREATE INDEX argument_signature ON arguments(signature,conclusion);
                CREATE VIRTUAL TABLE search USING fts5(id UNINDEXED, text, tokenize='unicode61');
            ''')
            records = []
            for path in inputs(root):
                raw = path.read_bytes()
                db.execute('INSERT INTO source_files VALUES (?,?)',
                           (path.relative_to(root).as_posix(), raw))
                record = json.loads(raw)
                for kind, entity in entities(path, record):
                    records.append((path, kind, entity))
            known = {record['id'] for _, _, record in records}
            for path, kind, record in records:
                identifier = record['id']
                body = json.dumps(record, ensure_ascii=False, sort_keys=True)
                key = kind + ':' + identifier
                db.execute('INSERT INTO records VALUES (?,?,?,?,?)',
                           (key, identifier, kind, path.relative_to(root).as_posix(), body))
                db.execute('INSERT INTO search VALUES (?,?)', (key, body))
                db.executemany('INSERT OR IGNORE INTO refs VALUES (?,?)',
                               ((key, ref) for ref in references(record) if ref in known and ref != identifier))
                if kind == 'arguments':
                    signature = json.dumps(sorted(set(record.get('premise_statement_ids', []))))
                    db.execute('INSERT INTO arguments VALUES (?,?,?)',
                               (identifier, signature, record.get('conclusion_statement_id')))
            if before != digest(root):
                raise ValueError('corpus changed while indexing; retry')
            db.executemany('INSERT INTO metadata VALUES (?,?)', [('schema', SCHEMA), ('digest', before)])
            db.commit()
        finally:
            db.close()
        temporary.replace(destination)
    finally:
        temporary.unlink(missing_ok=True)


def connect(root, path):
    db = sqlite3.connect(path.resolve().as_uri() + '?mode=ro', uri=True)
    db.row_factory = sqlite3.Row
    metadata = dict(db.execute('SELECT key,value FROM metadata'))
    if metadata.get('schema') != SCHEMA or metadata.get('digest') != digest(root):
        db.close()
        raise ValueError('index is stale; run build again')
    return db


def record(db, identifier):
    rows = db.execute('SELECT body FROM records WHERE id=? OR key=?', (identifier, identifier)).fetchall()
    if len(rows) > 1:
        raise ValueError('ambiguous ID; use kind:ID, for example results:' + identifier)
    row = rows[0] if rows else None
    if row is None:
        raise ValueError(f'unknown record: {identifier}')
    return json.loads(row['body'])


def lookup(db, identifier):
    return {'record': record(db, identifier), 'referenced_by': [dict(row) for row in db.execute(
        'SELECT r.id,r.kind,r.path FROM refs JOIN records r ON r.key=refs.owner WHERE target=? ORDER BY r.kind,r.id',
        (identifier.split(':', 1)[-1],))]}


def duplicates(db):
    """Exact statement-ID matches only; no semantic equivalence or redundancy claim."""
    groups = db.execute('SELECT signature,conclusion FROM arguments GROUP BY signature,conclusion HAVING count(*)>1')
    return [{'premise_statement_ids': json.loads(row['signature']), 'conclusion_statement_id': row['conclusion'],
             'argument_ids': [item[0] for item in db.execute(
                 'SELECT id FROM arguments WHERE signature=? AND conclusion=? ORDER BY id',
                 (row['signature'], row['conclusion']))]} for row in groups]


def bundle(db, case_id, premises):
    """Reuse the existing profile-specific engine, strictly in registered-only mode."""
    from configurations import configuration_report
    case = record(db, case_id)
    if 'semantics' not in case or 'configurations' not in case:
        raise ValueError('bundle requires a configuration case ID')
    unknown = set(premises) - case['semantics']['applications'].keys()
    if unknown:
        raise ValueError('statements outside selected profile: ' + ', '.join(sorted(unknown)))
    tables = {kind: {row['id']: json.loads(row['body']) for row in db.execute(
        'SELECT id,body FROM records WHERE kind=?', (kind,))} for kind in ('results', 'arguments', 'models')}
    report = configuration_report(case, tables['results'], tables['arguments'], tables['models'],
                                  selection={'id': 'query', 'statement_ids': sorted(set(premises))})
    # Surface only directly applicable registered rules. Composition and certification
    # remain owned by corpus.py configurations / configuration-report.
    rules = []
    for rid in case.get('implication_result_ids', []):
        result = tables['results'][rid]
        argument = tables['arguments'][result['argument_id']]
        if set(argument['premise_statement_ids']) <= set(premises):
            rules.append({'result_id': rid, 'theorem': result['theorem'],
                          'premise_statement_ids': argument['premise_statement_ids'],
                          'conclusion_statement_id': argument['conclusion_statement_id']})
    return {'mode': 'registered-only', 'certification': 'Not verification evidence. Use existing configuration verification commands.',
            'applicable_registered_implications': rules, 'report': report}


def compare(db, case_id, left, right):
    """Candidate strength comparison; requires the existing proof gate to certify."""
    from configurations import implication_closure
    # Validate membership and reuse the same exact registered profile for both sides.
    bundle(db, case_id, left)
    bundle(db, case_id, right)
    case = record(db, case_id)
    tables = {kind: {row['id']: json.loads(row['body']) for row in db.execute(
        'SELECT id,body FROM records WHERE kind=?', (kind,))} for kind in ('results', 'arguments')}
    def direction(source, target):
        closure = implication_closure(set(source), case, tables['results'], tables['arguments'], include_assumptions=True)
        for item in closure['items']:
            item['minimality'] = 'minimal supports from registered rules only; verification required'
        found = {item['statement_id'] for item in closure['items']}
        return {'registered_paths_cover_target': set(target) <= found,
                'missing_statement_ids': sorted(set(target) - found), 'closure': closure}
    return {'mode': 'registered-only candidate comparison', 'case_id': case_id,
            'warning': 'Paths require verification. Missing paths do not prove non-entailment or strict strength.',
            'left_to_right': direction(left, right), 'right_to_left': direction(right, left)}


def related(db, identifier, limit=20):
    """Rank propositions by explicit connections, vocabulary, then prose overlap."""
    target = record(db, identifier)
    sid = target['id']
    rows = {row['id']: dict(row) for row in db.execute(
        "SELECT id,path,body FROM records WHERE kind='statements'")}
    if sid not in rows or (':' in identifier and not identifier.startswith('statements:')):
        raise ValueError('related requires a statement ID')
    statements = {key: json.loads(row['body']) for key, row in rows.items()}
    evidence = {}
    def add(other, tier, reason):
        if other in statements and other != sid:
            entry = evidence.setdefault(other, {'tier': tier, 'reasons': []})
            entry['tier'] = min(entry['tier'], tier)
            entry['reasons'].append(reason)
    results = {}
    for row in db.execute("SELECT body FROM records WHERE kind='results'"):
        value = json.loads(row['body'])
        results.setdefault(value.get('argument_id'), []).append(
            {key: value.get(key) for key in ('id', 'theorem', 'status')})
    for row in db.execute("SELECT body,path FROM records WHERE kind='arguments'"):
        arg = json.loads(row['body'])
        premises = arg.get('premise_statement_ids', [])
        conclusion = arg.get('conclusion_statement_id')
        if sid not in premises and sid != conclusion:
            continue
        for other in set(premises + ([conclusion] if conclusion else [])) - {sid}:
            role = ('incompatible_bundle_member' if conclusion == 'STMT-CONFIGURATION-FALSE' and other in premises else
                    'joint_premise' if sid in premises and other in premises else
                    'consequence_with_full_bundle' if sid in premises else 'supporting_premise')
            add(other, 0, {'kind': role, 'argument_id': arg['id'], 'path': row['path'],
                           'premise_statement_ids': premises, 'conclusion_statement_id': conclusion,
                           'results': results.get(arg['id'], []),
                           'qualification': 'Recorded argument; all premises are retained. Not newly verified.'})
    for row in db.execute("SELECT body,path FROM records WHERE kind='relations'"):
        relation = json.loads(row['body'])
        a, b = relation.get('subject_id'), relation.get('object_id')
        if sid in (a, b):
            add(b if sid == a else a, 1, {'kind': 'recorded_relation', 'relation_id': relation['id'],
                'predicate': relation.get('predicate'), 'subject_id': a, 'object_id': b,
                'path': row['path'], 'qualification': 'Recorded semantic relation, not a proof of entailment.'})
    for other, statement in statements.items():
        for field in ('definition_ids', 'disambiguation_ids'):
            shared = sorted(set(target.get(field, [])) & set(statement.get(field, [])))
            if shared:
                add(other, 2, {'kind': 'shared_' + field, 'ids': shared})
        declaration = target.get('lean_declaration', '')
        candidate = statement.get('lean_declaration', '')
        if declaration and declaration == candidate:
            add(other, 2, {'kind': 'same_lean_declaration', 'declaration': declaration,
                           'qualification': 'Check parameterization and readings before claiming equivalence.'})
        elif declaration.count('.') >= 3 and declaration.rsplit('.', 1)[0] == candidate.rsplit('.', 1)[0]:
            add(other, 2, {'kind': 'shared_lean_namespace', 'namespace': declaration.rsplit('.', 1)[0],
                           'qualification': 'Module proximity only; no type or predicate equivalence inferred.'})
    stop = set('a an the is are of to and or in for that this its it with by from as not every all some only has have be being'.split())
    def words(value):
        return {word for word in re.findall(r'[a-z][a-z0-9]+', value.lower()) if word not in stop}
    tokens = {key: words(value.get('paraphrase', '')) for key, value in statements.items()}
    counts = Counter(word for group in tokens.values() for word in group)
    text_scores = {}
    for other, group in tokens.items():
        overlap = tokens[sid] & group
        if len(overlap) >= 2:
            score = sum(math.log(1 + len(tokens) / counts[word]) for word in overlap)
            text_scores[other] = score
            add(other, 3, {'kind': 'text_overlap', 'words': sorted(overlap),
                           'qualification': 'Discovery heuristic only; no logical relationship established.'})
    def bundle_size(key):
        return min((len(reason['premise_statement_ids']) for reason in evidence[key]['reasons']
                    if 'premise_statement_ids' in reason), default=1000000)
    ranked = sorted(evidence, key=lambda key: (evidence[key]['tier'], bundle_size(key),
        -sum(len(reason.get('ids', [])) for reason in evidence[key]['reasons']),
        -text_scores.get(key, 0), key))
    matches = []
    for other in ranked[:max(1, min(limit, 200))]:
        entry = evidence[other]
        reasons = sorted(entry['reasons'], key=lambda reason: (
            0 if 'argument_id' in reason else 1, len(reason.get('premise_statement_ids', []))))
        matches.append({'statement_id': other, 'paraphrase': statements[other].get('paraphrase'),
                        'path': rows[other]['path'], 'tier': entry['tier'],
                        'reason_count': len(reasons), 'reasons': reasons})
    prior = [dict(row) for row in db.execute(
        "SELECT r.id,r.path,r.body FROM refs JOIN records r ON r.key=refs.owner "
        "WHERE refs.target=? AND r.kind='attempts' ORDER BY r.id", (sid,))]
    for attempt in prior:
        body = json.loads(attempt.pop('body'))
        attempt.update(outcome=body.get('outcome'), summary=body.get('summary'), blocker=body.get('blocker'))
    return {'statement_id': sid, 'mode': 'discovery, not certification',
            'ranking': ['recorded argument connections (smaller premise bundles first)', 'recorded semantic relations',
                        'shared definitions/disambiguations/declaration or namespace', 'weighted paraphrase overlap'],
            'candidate_count': len(evidence), 'matches': matches, 'prior_attempts': prior,
            'scope': 'No automatic equivalence, strengthening, contradiction or cross-profile composition is inferred.'}


def cached_related(root, identifier, limit=20):
    """Workflow entry: refresh disposable lookup data, never proof preparation."""
    path = root / '.cache/research-index.sqlite'
    if not path.exists():
        build(root, path)
    try:
        db = connect(root, path)
    except ValueError as exc:
        if str(exc) != 'index is stale; run build again':
            raise
        build(root, path)
        db = connect(root, path)
    try:
        return related(db, identifier, limit)
    finally:
        db.close()


def parity(db, root):
    """Compare source coverage, exact bytes and queryable records independently."""
    files = {row['path']: bytes(row['content']) for row in db.execute('SELECT path,content FROM source_files')}
    current = {path.relative_to(root).as_posix(): path.read_bytes() for path in inputs(root)}
    issues = []
    for path in sorted(files.keys() | current.keys()):
        if files.get(path) != current.get(path):
            issues.append({'path': path, 'issue': 'missing or unequal source bytes'})
    expected = {}
    nonrecords = []
    for path, raw in current.items():
        value = json.loads(raw)
        projected = list(entities(Path(path), value))
        for kind, entity in projected:
            expected[kind + ':' + entity['id']] = entity
        if not projected:
            nonrecords.append(path)
    indexed = {row['key']: json.loads(row['body']) for row in db.execute('SELECT key,body FROM records')}
    for path in sorted(expected.keys() | indexed.keys()):
        if expected.get(path) != indexed.get(path):
            issues.append({'path': path, 'issue': 'missing or unequal query record'})
    return {'status': 'equal' if not issues else 'mismatch',
            'source_files': len(current), 'queryable_records': len(expected),
            'preserved_nonrecord_files': nonrecords, 'issues': issues,
            'scope': 'Storage and record parity only; not proof verification or complete CLI feature parity.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=ROOT)
    sub = parser.add_subparsers(dest='command', required=True)
    sub.add_parser('build')
    search = sub.add_parser('search')
    search.add_argument('query', help='literal words; all words must match')
    search.add_argument('--limit', type=int, default=20)
    show = sub.add_parser('show')
    show.add_argument('id')
    sub.add_parser('duplicates')
    sub.add_parser('summary')
    related_parser = sub.add_parser('related')
    related_parser.add_argument('id')
    related_parser.add_argument('--limit', type=int, default=20)
    sub.add_parser('parity')
    export = sub.add_parser('export')
    export.add_argument('path', help='exact corpus-relative source path; writes original bytes to stdout')
    query = sub.add_parser('bundle')
    query.add_argument('--case', required=True)
    query.add_argument('--premise', action='append', default=[])
    comparison = sub.add_parser('compare')
    comparison.add_argument('--case', required=True)
    comparison.add_argument('--left', action='append', default=[])
    comparison.add_argument('--right', action='append', default=[])
    args = parser.parse_args()
    root = args.root.resolve()
    destination = root / '.cache/research-index.sqlite'
    try:
        if args.command == 'build':
            build(root, destination)
            output = {'index': str(destination), 'mode': 'derived lookup only'}
        else:
            db = connect(root, destination)
            try:
                if args.command == 'export':
                    import sys
                    row = db.execute('SELECT content FROM source_files WHERE path=?', (args.path,)).fetchone()
                    if row is None:
                        raise ValueError('unknown indexed path: ' + args.path)
                    sys.stdout.buffer.write(row['content'])
                    return
                elif args.command == 'parity':
                    output = parity(db, root)
                    if output['issues']:
                        raise ValueError(json.dumps(output))
                elif args.command == 'search':
                    words = args.query.split()
                    if not words:
                        raise ValueError('search requires at least one word')
                    expression = ' AND '.join('"' + word.replace('"', '""') + '"' for word in words)
                    output = [dict(row) for row in db.execute(
                        'SELECT r.id,r.kind,r.path FROM search JOIN records r ON r.key=search.id WHERE search MATCH ? ORDER BY rank LIMIT ?',
                        (expression, max(1, min(args.limit, 200))))]
                elif args.command == 'related':
                    output = related(db, args.id, args.limit)
                elif args.command == 'show':
                    output = lookup(db, args.id)
                elif args.command == 'duplicates':
                    output = duplicates(db)
                elif args.command == 'compare':
                    output = compare(db, args.case, args.left, args.right)
                elif args.command == 'bundle':
                    output = bundle(db, args.case, args.premise)
                else:
                    output = {'mode': 'registered inventory, not certified progress',
                              'records_by_kind': {row[0]: row[1] for row in db.execute('SELECT kind,count(*) FROM records GROUP BY kind')},
                              'exact_duplicate_argument_groups': len(duplicates(db))}
            finally:
                db.close()
        print(json.dumps(output, indent=2, ensure_ascii=False))
    except (ValueError, OSError, sqlite3.Error) as exc:
        parser.exit(1, f'research index: {exc}\n')


if __name__ == '__main__':
    main()
