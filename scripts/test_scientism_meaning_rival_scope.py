#!/usr/bin/env python3
"""Actual-record scope guards; hypothetical refutations are test inputs only."""
import copy
import json
import sys
import unittest
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
import corpus
from corpus_ids import legacy_uuid  # noqa: E402
ROOT = Path(__file__).resolve().parent.parent


def record(kind, key):
    for path in (ROOT / 'corpus' / kind).glob('*.json'):
        item = json.loads(path.read_text())
        if item['id'] == key:
            return item
    raise AssertionError(key)


class ScopedRivalTest(unittest.TestCase):
    def counterfactual(self, raw, target, edge):
        relation = record('relations', edge)
        ids = {raw, target, relation['subject_id']}
        statements = [record('statements', key) for key in ids]
        for item in statements:
            item.pop('self_evident', None)
        statements.append({'id': 'TEST-NOT-RAW', 'paraphrase': 'Hypothetical only'})
        argument = {'id': 'TEST-REFUTATION', 'premise_statement_ids': [],
                    'conclusion_statement_id': 'TEST-NOT-RAW', 'inference_ids': []}
        refutation = {'id': 'TEST-REFUTES', 'subject_kind': 'argument',
            'subject_id': argument['id'], 'predicate': 'refutes',
            'object_kind': 'statement', 'object_id': raw}
        def report(rival):
            return corpus.frontier_report(copy.deepcopy(statements), [argument],
                [{'id': 'TEST-RESULT', 'argument_id': argument['id']}],
                [refutation, rival], root=target)
        fixed = report(relation)
        self.assertIn(raw, fixed['refuted_statements'])
        self.assertNotIn(target, fixed['closed_statements'])
        self.assertNotIn(target, fixed['established_statements'])
        legacy = dict(relation, subject_id=raw, predicate='alternative_to')
        self.assertEqual(report(legacy)['closed_statements'][target], 'alternatives_refuted')

    def test_scoped_scientism_is_not_universal_negative(self):
        edge = legacy_uuid('relation', 'REL-STRONG-SCIENTISM-ALTERNATIVE-TO-NON-EMPIRICAL-KNOWLEDGE')
        self.assertEqual(record('relations', edge)['subject_id'], legacy_uuid('statement', 'STMT-NO-NONEMPIRICAL-ESTABLISHED'))
        self.counterfactual(legacy_uuid('statement', 'STMT-STRONG-SCIENTISM'), legacy_uuid('statement', 'STMT-SOME-NON-EMPIRICAL-ESTABLISHED'), edge)
        argument = record('arguments', legacy_uuid('argument', 'SCIENTISM-SCOPE-GUARDED-NONEMPIRICAL-NEGATIVE'))
        self.assertEqual(set(argument['premise_statement_ids']),
            {legacy_uuid('statement', 'STMT-STRONG-SCIENTISM'), legacy_uuid('statement', 'STMT-SCIENTISM-EXISTENTIAL-NONEMPIRICAL-SCOPE')})

    def test_meaning_invariance_needs_actual_attitude_loss(self):
        edge = legacy_uuid('relation', 'REL-EXPRESSIVIST-MEANING-ALTERNATIVE-TO-EMOTIVIST-MEANING')
        self.assertEqual(record('relations', edge)['subject_id'], legacy_uuid('statement', 'STMT-EMOTIVIST-MEANING-FAILS'))
        self.counterfactual(legacy_uuid('statement', 'STMT-EXPRESSIVIST-MORAL-MEANING-INVARIANT'),
            legacy_uuid('statement', 'STMT-EMOTIVIST-MEANING-IS-EXPRESSED-ATTITUDE'), edge)
        argument = record('arguments', legacy_uuid('argument', 'INVARIANT-MEANING-WITH-ATTITUDE-LOSS-REFUTES-OCCASION'))
        self.assertEqual(set(argument['premise_statement_ids']), {
            legacy_uuid('statement', 'STMT-EXPRESSIVIST-MORAL-MEANING-INVARIANT'),
            legacy_uuid('statement', 'STMT-FREE-MORAL-ASSERTION-EXPRESSES-ATTITUDE'),
            legacy_uuid('statement', 'STMT-GEACH-ANTECEDENT-LACKS-FREE-STANDING-ATTITUDE'),
            legacy_uuid('statement', 'STMT-GEACH-MINOR-PREMISE-IS-MORAL')})

    def test_kripke_pu_raw_readings_remain_interpretive(self):
        edge = legacy_uuid('relation', 'REL-KRIPKE-NO-FACT-ALTERNATIVE-TO-PU-GRASP-NOT-INTERPRETATION')
        self.assertEqual(record('relations', edge)['predicate'], 'attacks')
        self.counterfactual(legacy_uuid('statement', 'STMT-KRIPKE-NO-FACT-OF-MEANING'),
            legacy_uuid('statement', 'STMT-PU-SOME-GRASP-OF-RULE-NOT-INTERPRETATION'), edge)


if __name__ == '__main__':
    unittest.main()
