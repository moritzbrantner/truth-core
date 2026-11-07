"""Offline tests for the bridge-candidate Lean trial driver (no Lean run)."""
import json
import unittest

import bridge_trial


REPORT = {"targets": [
    {"statement_id": "STMT-T", "lean_declaration": "N.T",
     "singles": [{"statement_ids": ["STMT-A"], "lean_declarations": ["N.A"], "score": 0.5},
                 {"statement_ids": ["STMT-B"], "lean_declarations": ["N.B"], "score": 0.4}],
     "pairs": [{"statement_ids": ["STMT-A", "STMT-B"], "lean_declarations": ["N.A", "N.B"], "score": 0.3}],
     "triples": []},
    {"statement_id": "STMT-S", "skipped": "no lean_declaration with exported constants"},
]}
MODULES = {"N.T": "M.T", "N.A": "M.A", "N.B": "M.A"}


class BridgeTrialTest(unittest.TestCase):
    def test_select_interleaves_arities_and_skips(self):
        chosen = bridge_trial.select(REPORT, 2)
        self.assertEqual([c["statement_ids"] for c in chosen], [["STMT-A"], ["STMT-A", "STMT-B"]])
        self.assertTrue(all(c["target_statement_id"] == "STMT-T" for c in chosen))

    def test_source_imports_modules_and_lists_trials(self):
        source = bridge_trial.lean_source(bridge_trial.select(REPORT, 3), MODULES, 1000)
        lines = source.splitlines()
        self.assertEqual(lines[:3], ["import Aesop", "import M.A", "import M.T"])
        self.assertIn("set_option maxHeartbeats 1000", lines)
        self.assertIn('#bridge_try "1" N.T from N.A N.B', lines)
        with self.assertRaises(ValueError):
            bridge_trial.lean_source(bridge_trial.select(REPORT, 1), {}, 1000)
        bad = [{"target_declaration": "N.T; evil", "lean_declarations": []}]
        with self.assertRaises(ValueError):
            bridge_trial.lean_source(bad, {"N.T; evil": "M"}, 1000)

    def test_parse_classifies_controls(self):
        trials = bridge_trial.select(REPORT, 3)
        def line(label, **fields):
            return "f.lean:1:0: info: BRIDGE-JSON " + json.dumps({"label": str(label), "generalized": [], **fields})
        output = "\n".join([
            line(0, closed_by="aesop", premises_refuted_by=None, target_alone_closed_by=None),
            line(1, closed_by="grind", premises_refuted_by=None, target_alone_closed_by="grind"),
        ])
        rows = bridge_trial.parse(output, trials)
        self.assertEqual([r["status"] for r in rows], ["closed", "closed_without_premises", "error"])
        self.assertEqual(bridge_trial.classify({"closed_by": "aesop", "generalized": ["N.A.x"]}),
                         "closed_generalized")
        self.assertEqual(bridge_trial.classify({"closed_by": "aesop", "premises_refuted_by": "simp_all"}),
                         "closed_vacuous")
        self.assertEqual(bridge_trial.classify({"closed_by": None}), "open")


if __name__ == "__main__":
    unittest.main()
