import unittest
from research_comparisons import validate_comparisons


class ComparisonTests(unittest.TestCase):
    def cell(self, **changes):
        return dict(target_statement_id='P', rival_statement_id='R', sense_definition_id='D',
                    outcome='excluded', conditions='EM and rotating existence', scope='same profile and world',
                    coverage='only the nine enum constructors', exclusivity='one constructor per use',
                    next_step='test rejecting EM', **changes)

    def test_optional_and_explicit(self):
        validate_comparisons({}, {'P', 'R'}, {'D'})
        validate_comparisons({'research_comparisons': [self.cell()]}, {'P', 'R'}, {'D'})

    def test_reject_missing_links_scope_and_witness(self):
        for change in ({'rival_statement_id': 'unknown'}, {'sense_definition_id': 'unknown'},
                       {'scope': ''}, {'outcome': 'proved'}, {'outcome': 'model-witnessed'},
                       {'outcome': 'unresolved'}):
            cell = self.cell()
            cell.update(change)
            with self.assertRaises(ValueError):
                validate_comparisons({'research_comparisons': [cell]}, {'P', 'R'}, {'D'})

    def test_compatible_requires_witness_and_open_requires_gap(self):
        for outcome, field in [('model-witnessed', 'witness'), ('unresolved', 'gap')]:
            cell = self.cell()
            cell.update(outcome=outcome, **{field: 'exact certificate or missing bridge'})
            validate_comparisons({'research_comparisons': [cell]}, {'P', 'R'}, {'D'})
