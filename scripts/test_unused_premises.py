"""Offline tests for `corpus.py unused-premises` (#571), on synthetic reports."""

from __future__ import annotations

import unittest

import corpus


def bound(result_id: str, premises: list[dict], status: str = "bound") -> dict:
    return {"id": result_id, "theorem": f"T.{result_id}", "status": status, "premises": premises}


def premise(statement_id: str, position: int, **bundle: object) -> dict:
    entry = {"hypothesis": f"h{statement_id}", "position": position, "statement_id": statement_id}
    entry.update(bundle)
    return entry


def usage(result_id: str, hypotheses: list[dict]) -> dict:
    return {"theorem": f"T.{result_id}", "hypotheses": hypotheses}


def hyp(position: int, used: bool, conjuncts: list[bool] | str | None = None) -> dict:
    entry = {"position": position, "name": f"h{position}", "used": used}
    if conjuncts is not None:
        entry["conjuncts_used"] = conjuncts
    return entry


class UnusedPremiseFindingsTest(unittest.TestCase):
    def test_all_premises_used_gives_no_finding(self):
        report = corpus.unused_premise_findings(
            [bound("R", [premise("P", 1), premise("Q", 2)])],
            [usage("R", [hyp(1, True), hyp(2, True)])],
        )
        self.assertEqual(report["findings"], [])
        self.assertEqual(report["summary"], {"checked": 1, "findings": 0, "skipped": 0})

    def test_unused_plain_hypothesis_is_reported_with_root_flag(self):
        report = corpus.unused_premise_findings(
            [bound("R", [premise("P", 1), premise("Q", 2)])],
            [usage("R", [hyp(1, True), hyp(2, False)])],
            root_open={"Q"},
        )
        self.assertEqual(
            report["findings"],
            [{"result_id": "R", "theorem": "T.R", "hypothesis": "hQ", "statement_id": "Q", "open_on_root_path": True}],
        )

    def test_bundle_conjuncts_are_checked_individually(self):
        report = corpus.unused_premise_findings(
            [bound("R", [
                premise("A", 1, bundle="T.Theory", conjunct=0),
                premise("B", 1, bundle="T.Theory", conjunct=1),
            ])],
            [usage("R", [hyp(1, True, [True, False])])],
        )
        self.assertEqual([f["statement_id"] for f in report["findings"]], ["B"])
        self.assertEqual(report["findings"][0]["conjunct"], 1)
        self.assertFalse(report["findings"][0]["open_on_root_path"])

    def test_unfoldable_bundle_counts_as_used(self):
        report = corpus.unused_premise_findings(
            [bound("R", [premise("A", 1, bundle="T.Theory", conjunct=0)])],
            [usage("R", [hyp(1, False, "cannot unfold")])],
        )
        self.assertEqual(report["findings"], [])

    def test_mismatched_or_undescribed_results_are_skipped(self):
        report = corpus.unused_premise_findings(
            [bound("R", [premise("P", 1)], status="mismatch"), bound("S", [premise("P", 1)])],
            [usage("R", [hyp(1, False)])],
        )
        self.assertEqual(report["findings"], [])
        self.assertEqual(report["skipped"], ["R", "S"])
        self.assertEqual(report["summary"]["checked"], 0)


if __name__ == "__main__":
    unittest.main()
