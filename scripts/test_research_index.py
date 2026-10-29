"""Boundary tests for the disposable research index."""
import json
from pathlib import Path
import tempfile
import unittest

from research_index import build, connect, duplicates, lookup, record, bundle, compare, parity, related, cached_related


class ResearchIndexTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.path = self.root / '.cache/index.sqlite'
        self.put('statements', {'id': 'S', 'paraphrase': 'a statement'})
        self.put('arguments', {'id': 'A', 'premise_statement_ids': ['S'], 'conclusion_statement_id': 'T'})
        self.put('arguments', {'id': 'B', 'premise_statement_ids': ['S'], 'conclusion_statement_id': 'T'})
        self.put('results', {'id': 'A', 'argument_id': 'A'})

    def put(self, kind, value):
        directory = self.root / 'corpus' / kind
        directory.mkdir(parents=True, exist_ok=True)
        (directory / (value['id'] + '.json')).write_text(json.dumps(value))

    def open(self):
        build(self.root, self.path)
        db = connect(self.root, self.path)
        self.addCleanup(db.close)
        return db

    def test_namespaced_identity_and_reverse_links(self):
        db = self.open()
        with self.assertRaisesRegex(ValueError, 'ambiguous'):
            record(db, 'A')
        self.assertEqual(record(db, 'results:A')['argument_id'], 'A')
        self.assertEqual({r['id'] for r in lookup(db, 'S')['referenced_by']}, {'A', 'B'})
        self.assertEqual(duplicates(db)[0]['argument_ids'], ['A', 'B'])

    def test_same_id_result_references_its_argument_without_identity_self_links(self):
        db = self.open()
        references = lookup(db, 'arguments:A')['referenced_by']
        self.assertEqual([(item['kind'], item['id']) for item in references], [('results', 'A')])
        self.assertEqual(lookup(db, 'arguments:B')['referenced_by'], [])

    def test_corpus_edit_rejects_stale_queries(self):
        self.open()
        self.put('statements', {'id': 'S', 'paraphrase': 'changed'})
        with self.assertRaisesRegex(ValueError, 'stale'):
            connect(self.root, self.path)

    def test_profile_boundary_and_uncertified_status(self):
        self.put('configurations', {'id': 'CONFIG-X', 'seed_statement_id': 'S',
                  'semantics': {'applications': {'S': []}}, 'configurations': []})
        db = self.open()
        with self.assertRaisesRegex(ValueError, 'outside selected profile'):
            bundle(db, 'CONFIG-X', ['T'])
        output = bundle(db, 'CONFIG-X', ['S'])
        comparison = compare(db, 'CONFIG-X', ['S'], ['S'])
        self.assertTrue(comparison['left_to_right']['registered_paths_cover_target'])
        self.assertIn('verification required', comparison['left_to_right']['closure']['items'][0]['minimality'])
        self.assertFalse(output['report']['verified'])
        self.assertEqual(output['report']['configurations'][0]['status'], 'verification required')

    def test_full_file_and_record_parity(self):
        path = self.root / 'corpus/schema.json'
        raw = b'{ "title": "schema without an entity ID" }\n'
        path.write_bytes(raw)
        db = self.open()
        report = parity(db, self.root)
        self.assertEqual(report['status'], 'equal')
        self.assertEqual(report['preserved_nonrecord_files'], ['corpus/schema.json'])
        self.assertEqual(db.execute('SELECT content FROM source_files WHERE path=?',
                                   ('corpus/schema.json',)).fetchone()[0], raw)

    def test_related_ranks_arguments_and_preserves_joint_premises(self):
        self.put('statements', {'id': 'S', 'paraphrase': 'distinctive causal explanation',
                               'definition_ids': ['DEF-X']})
        self.put('statements', {'id': 'T', 'paraphrase': 'different conclusion'})
        self.put('statements', {'id': 'U', 'paraphrase': 'distinctive causal explanation',
                               'definition_ids': ['DEF-X']})
        self.put('statements', {'id': 'V', 'paraphrase': 'distinctive causal explanation'})
        self.put('arguments', {'id': 'A', 'premise_statement_ids': ['S', 'U'],
                               'conclusion_statement_id': 'T'})
        self.put('attempts', {'id': 'ATTEMPT-X', 'statement_ids': ['S'], 'outcome': 'blocked'})
        db = self.open()
        output = related(db, 'S')
        matches = {item['statement_id']: item for item in output['matches']}
        self.assertEqual(matches['T']['tier'], 0)
        self.assertEqual(matches['V']['tier'], 3)
        reason = next(item for item in matches['T']['reasons'] if item['kind'] == 'consequence_with_full_bundle' and item['argument_id'] == 'A')
        self.assertEqual(reason['premise_statement_ids'], ['S', 'U'])
        self.assertEqual(reason['results'][0]['id'], 'A')
        self.assertEqual(output['prior_attempts'][0]['outcome'], 'blocked')
        self.assertNotIn('S', matches)
        with self.assertRaisesRegex(ValueError, 'statement ID'):
            related(db, 'results:A')

    def test_related_marks_conflicts_without_pairwise_negation(self):
        self.put('statements', {'id': 'T', 'paraphrase': 'another commitment'})
        self.put('statements', {'id': 'STMT-CONFIGURATION-FALSE', 'paraphrase': 'logical falsity'})
        self.put('arguments', {'id': 'CORE', 'premise_statement_ids': ['S', 'T', 'U'],
                               'conclusion_statement_id': 'STMT-CONFIGURATION-FALSE'})
        db = self.open()
        match = next(item for item in related(db, 'S')['matches'] if item['statement_id'] == 'T')
        reason = next(item for item in match['reasons'] if item.get('argument_id') == 'CORE')
        self.assertEqual(reason['kind'], 'incompatible_bundle_member')
        self.assertEqual(reason['premise_statement_ids'], ['S', 'T', 'U'])

    def test_json_keeps_all_reasons_while_text_is_bounded(self):
        from contextlib import redirect_stdout
        from io import StringIO
        from unittest.mock import patch
        import corpus
        self.put('statements', {'id': 'T', 'paraphrase': 'another commitment'})
        for index in range(5):
            self.put('arguments', {'id': f'EXTRA-{index}', 'premise_statement_ids': ['S'],
                                   'conclusion_statement_id': 'T'})
        output = StringIO()
        with patch.object(corpus, 'ROOT', self.root), redirect_stdout(output):
            self.assertEqual(corpus.main_with(['related', 'S', '--json']), 0)
        match = json.loads(output.getvalue())['matches'][0]
        self.assertEqual(match['reason_count'], 7)
        self.assertEqual(len(match['reasons']), 7)
        output = StringIO()
        with patch.object(corpus, 'ROOT', self.root), redirect_stdout(output):
            self.assertEqual(corpus.main_with(['related', 'S']), 0)
        self.assertEqual(output.getvalue().count('consequence_with_full_bundle:'), 3)
        self.assertIn('7 reasons total; showing 3 (all in --json)', output.getvalue())

    def test_workflow_cache_refresh_and_corpus_cli(self):
        from contextlib import redirect_stdout, redirect_stderr
        from io import StringIO
        from unittest.mock import patch
        import corpus
        cached_related(self.root, 'S')
        self.put('statements', {'id': 'T', 'paraphrase': 'newly indexed conclusion'})
        self.assertTrue(any(item['statement_id'] == 'T'
                            for item in cached_related(self.root, 'S')['matches']))
        output = StringIO()
        with patch.object(corpus, 'ROOT', self.root), redirect_stdout(output):
            self.assertEqual(corpus.main_with(['related', 'S', '--json']), 0)
        self.assertEqual(json.loads(output.getvalue())['statement_id'], 'S')
        with patch.object(corpus, 'ROOT', self.root), redirect_stderr(StringIO()):
            self.assertEqual(corpus.main_with(['related', 'MISSING']), 2)

    def test_nested_passages_keep_witness_and_become_searchable(self):
        directory = self.root / 'corpus/passages'
        directory.mkdir()
        value = {'snapshot': {'source_id': 'SOURCE', 'revision': 'pinned'},
                 'passages': [{'id': 'PASSAGE-1', 'locator': 'chapter 1'},
                              {'id': 'PASSAGE-2', 'locator': 'chapter 2'}]}
        (directory / 'collection.json').write_text(json.dumps(value))
        db = self.open()
        passage = lookup(db, 'PASSAGE-1')['record']
        self.assertEqual(passage['snapshot']['revision'], 'pinned')
        self.assertEqual(passage['passage']['locator'], 'chapter 1')
        self.assertEqual(parity(db, self.root)['status'], 'equal')
        self.assertEqual(len(list(db.execute("SELECT * FROM search WHERE search MATCH 'chapter'"))), 2)

    def test_parity_detects_corrupt_projection(self):
        self.open()
        import sqlite3
        from contextlib import closing
        with closing(sqlite3.connect(self.path)) as writer:
            writer.execute("UPDATE records SET body='{}' WHERE id='S'")
            writer.commit()
        db = connect(self.root, self.path)
        self.addCleanup(db.close)
        self.assertEqual(parity(db, self.root)['status'], 'mismatch')

    def test_failed_rebuild_preserves_previous_database(self):
        self.open()
        previous = self.path.read_bytes()
        path = self.root / 'corpus/statements/broken.json'
        path.write_text('{broken')
        with self.assertRaises(ValueError):
            build(self.root, self.path)
        self.assertEqual(self.path.read_bytes(), previous)


if __name__ == '__main__':
    unittest.main()
