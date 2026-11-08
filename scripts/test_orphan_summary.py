"""Orphan population and PR summary regression checks."""
import unittest
import subprocess
import tempfile
from pathlib import Path

from orphan_summary import base_count, orphan_count, summary, tree_count


class OrphanSummaryTests(unittest.TestCase):
    def test_population_matches_truth_orphans(self):
        arguments = [{"id": "connected", "conclusion_statement_id": "ROOT"},
                     {"id": "alternate", "conclusion_statement_id": "ALTERNATE"},
                     {"id": "idle", "conclusion_statement_id": "IDLE"}]
        results = [{"argument_id": arg, "status": status}
                   for arg, status in [("connected", "verified"),
                                       ("alternate", "solution-present"),
                                       ("idle", "verified"),
                                       ("idle", "solution-present"),
                                       ("idle", "pending"), ("missing", "verified")]]
        # Includes both verified statuses and counts results, not arguments;
        # alternate verified routes are connected too.
        self.assertEqual(orphan_count({"ROOT", "ALTERNATE"}, arguments, results), 2)
        self.assertEqual(orphan_count({"ROOT", "ALTERNATE", "IDLE"}, arguments, results), 0)

    def test_delta_sign_and_zero(self):
        for previous, expected in [(5, "-2"), (3, "+0"), (1, "+2")]:
            self.assertIn(f"| `BASE` | {previous} | 3 | {expected} |", summary("BASE", 3, previous))

    def test_unavailable_is_not_zero(self):
        report = summary("BASE", 3, None)
        self.assertIn("| `BASE` | unavailable | 3 | unavailable |", report)
        self.assertIn("No zero baseline", report)


class HistoricalSnapshotTests(unittest.TestCase):
    def test_transitive_refutation_support_and_historical_semantics(self):
        import inspect
        import corpus

        # Identical records on both revisions: only the available classifier
        # semantics change. The old module deliberately lacks relation loading.
        module_text = """
DEFAULT_FRONTIER_ROOT = 'ROOT'
def current_frontier(*args, **kwargs):
    return {'reaching_root_statements': ['ROOT']}
def load_dir(kind):
    records = {
        'arguments': [
            {'id': 'REF', 'premise_statement_ids': ['P'], 'conclusion_statement_id': 'NOT-R'},
            {'id': 'SUP', 'premise_statement_ids': ['Q'], 'conclusion_statement_id': 'P'},
            {'id': 'DEEP', 'premise_statement_ids': [], 'conclusion_statement_id': 'Q'},
            {'id': 'IDLE', 'premise_statement_ids': [], 'conclusion_statement_id': 'SIDE'}],
        'results': [{'argument_id': a, 'status': 'verified'} for a in ['REF', 'SUP', 'DEEP', 'IDLE']]}
    return [(None, r) for r in records[kind]]
"""
        relations_text = """
_old_load_dir = load_dir
def load_dir(kind):
    if kind != 'relations':
        return _old_load_dir(kind)
    return [(None, r) for r in [
        {'predicate': 'alternative_to', 'subject_kind': 'statement', 'subject_id': 'R', 'object_kind': 'statement', 'object_id': 'ROOT'},
        {'predicate': 'refutes', 'subject_kind': 'argument', 'subject_id': 'REF', 'object_kind': 'statement', 'object_id': 'R'}]]
"""
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'scripts').mkdir()
            module = root / 'scripts' / 'corpus.py'
            module.write_text(module_text)
            for args in [('init', '-q'), ('add', '.'),
                         ('-c', 'user.name=Test', '-c', 'user.email=test@example.org',
                          'commit', '-qm', 'historical classifier')]:
                subprocess.run(['git', *args], cwd=root, check=True, capture_output=True)
            module.write_text(module_text + relations_text + inspect.getsource(corpus.refutation_support))
            # Refuter and two generations of premise support connect; IDLE stays orphaned.
            self.assertEqual(tree_count(root), 1)
            # Historical revisions keep the old semantics, even on identical records.
            self.assertEqual(base_count(root, 'HEAD'), 4)
            subprocess.run(['git', 'add', '.'], cwd=root, check=True)
            subprocess.run(['git', '-c', 'user.name=Test', '-c', 'user.email=test@example.org',
                            'commit', '-qm', 'conditional support'], cwd=root, check=True, capture_output=True)
            self.assertEqual(base_count(root, 'HEAD'), 1)

    def test_archive_uses_historical_records_and_missing_revision_fails(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "scripts").mkdir()
            module = root / "scripts" / "corpus.py"
            module.write_text("""
DEFAULT_FRONTIER_ROOT = 'ROOT'
def current_frontier(root, reaching_root, **kwargs):
    assert root == 'ROOT'
    return {'reaching_root_statements': ['ROOT']}
def load_dir(kind):
    records = {'arguments': [{'id': 'A', 'conclusion_statement_id': 'IDLE'}],
               'results': [{'argument_id': 'A', 'status': 'verified'}]}
    return [(None, r) for r in records[kind]]
""")
            for args in [("init", "-q"), ("add", "."),
                         ("-c", "user.name=Test", "-c", "user.email=test@example.org",
                          "commit", "-qm", "fixture")]:
                subprocess.run(["git", *args], cwd=root, check=True, capture_output=True)
            module.write_text(module.read_text().replace("'IDLE'", "'ROOT'"))
            self.assertEqual(tree_count(root), 0)
            self.assertEqual(base_count(root, "HEAD"), 1)
            with self.assertRaises(subprocess.CalledProcessError):
                base_count(root, "missing-revision")
            module.write_text("DEFAULT_FRONTIER_ROOT = 'ROOT'\ndef current_frontier(*a, **k): return {}\n")
            with self.assertRaises(subprocess.CalledProcessError):
                tree_count(root)
