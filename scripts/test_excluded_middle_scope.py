#!/usr/bin/env python3
"""Focused actual-record regression for the EM policy/global-denial boundary."""
from __future__ import annotations

import copy
import json
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import corpus

ROOT = Path(__file__).resolve().parent.parent
EM = "STMT-EXCLUDED-MIDDLE"
GLOBAL_DENIAL = "STMT-NOT-EXCLUDED-MIDDLE"
INSTANCE_DENIAL = "STMT-SOME-EXCLUDED-MIDDLE-INSTANCE-FAILS"
WITHHELD = "STMT-EXCLUDED-MIDDLE-WITHHELD-INTUITIONISM"
ASSERTED = "STMT-ALL-EXCLUDED-MIDDLE-INSTANCES-ASSERTED"


def record(kind: str, record_id: str) -> dict:
    for path in (ROOT / "corpus" / kind).glob("*.json"):
        item = json.loads(path.read_text())
        if item["id"] == record_id:
            return item
    raise AssertionError(f"missing actual record {record_id}")


class ExcludedMiddleScopeTest(unittest.TestCase):
    def report(self, floor: bool, global_rival: bool = True) -> dict:
        ids = [EM, GLOBAL_DENIAL, INSTANCE_DENIAL, WITHHELD, ASSERTED,
               "STMT-EXCLUDED-MIDDLE-NOT-DENIABLE"]
        statements = [record("statements", item) for item in ids]
        if not floor:
            next(item for item in statements if item["id"] == EM).pop("self_evident")
        relations = [record("relations", item) for item in [
            "REL-INTUITIONISM-ALTERNATIVE-TO-EXCLUDED-MIDDLE",
            "REL-EXCLUDED-MIDDLE-DENIAL-ALTERNATIVE-TO-EXCLUDED-MIDDLE",
            "REL-NOT-DENIABLE-REFUTES-EXCLUDED-MIDDLE-DENIAL",
            "REL-NOT-EXCLUDED-MIDDLE-ALTERNATIVE-TO-EXCLUDED-MIDDLE",
        ]]
        if not global_rival:
            relations = [item for item in relations if item["subject_id"] != GLOBAL_DENIAL]
        return corpus.frontier_report(
            copy.deepcopy(statements),
            [record("arguments", "LOGIC-EXCLUDED-MIDDLE-NOT-DENIABLE")],
            [record("results", "LOGIC-EXCLUDED-MIDDLE-NOT-DENIABLE")],
            relations, root=EM,
        )

    def test_policy_rival_targets_assertion_not_logical_holding(self):
        relation = record("relations", "REL-INTUITIONISM-ALTERNATIVE-TO-EXCLUDED-MIDDLE")
        self.assertEqual(relation["subject_id"], WITHHELD)
        self.assertEqual(relation["object_id"], ASSERTED)

    def test_no_legacy_floor_does_not_make_instance_refutation_prove_em(self):
        report = self.report(floor=False)
        self.assertNotIn(EM, report["closed_statements"])
        self.assertNotIn(EM, report["established_statements"])
        self.assertNotIn(GLOBAL_DENIAL, report["refuted_statements"])
        # Show that this fixture actually catches the removed-rival false closure.
        unsafe = self.report(floor=False, global_rival=False)
        self.assertEqual(unsafe["closed_statements"][EM], "alternatives_refuted")

    def test_existing_legacy_floor_still_has_its_original_authority(self):
        report = self.report(floor=True)
        self.assertEqual(report["closed_statements"][EM], "self_evident")
        self.assertIn(EM, report["established_statements"])
        self.assertNotIn(GLOBAL_DENIAL, report["refuted_statements"])


if __name__ == "__main__":
    unittest.main()
