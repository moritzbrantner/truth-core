#!/usr/bin/env python3
"""Offline behavior tests for the read-only issue acceptance projection."""

import contextlib
import io
import json
import tempfile
import unittest
from pathlib import Path

import corpus
from issue_acceptance import analyze_issues, issues_for_id


def issue(number, body="", **extra):
    return {"number": number, "title": f"Research #{number}", "body": body,
            "url": f"https://github.com/moritzbrantner/truth-core/issues/{number}", **extra}


def acceptance(body):
    return f"Notes before the contract.\n\n```truth-core-acceptance\n{body}\n```\n"


def records():
    return {
        "results": [{"id": "RESULT-1", "theorem": "TruthCore.Demo.proof", "status": "solution-present"},
                    {"id": "RESULT-PENDING", "theorem": "TruthCore.Demo.pending", "status": "pending"}],
        "statements": [{"id": "STMT-P"}, {"id": "STMT-Q"}, {"id": "STMT-R"}],
        "claims": [{"id": "CLAIM-Q", "statement_id": "STMT-Q", "source_id": "SOURCE-1", "locator": "section 1"}],
        "configurations": [{"id": "CONFIG-1"}],
        "attempts": [{"id": "ATTEMPT-1", "outcome": "failed"}],
    }


class IssueAcceptanceTests(unittest.TestCase):
    def test_delivered_missing_and_untracked_are_distinct(self):
        items = [
            issue(9, acceptance("results: [RESULT-1]\ntheorems: [TruthCore.Demo.proof]\n"
                                "statements: [STMT-P: proved, STMT-Q: sourced]\n"
                                "configurations: [CONFIG-1]\nattempts: [ATTEMPT-1]")),
            issue(10, acceptance("results: [RESULT-PENDING]\nstatements: [STMT-R: closed]")),
            issue(11, "Needs research; no acceptance block yet."),
        ]
        report = analyze_issues(items, records(), {"STMT-P": "proved"})
        self.assertEqual([(item["number"], item["status"]) for item in report["issues"]],
                         [(9, "delivered"), (10, "missing"), (11, "untracked")])
        self.assertEqual(report["summary"], {"delivered": 1, "missing": 1, "malformed": 0, "untracked": 1})
        self.assertEqual([entry["id"] for entry in report["issues"][1]["requirements"] if not entry["met"]],
                         ["RESULT-PENDING", "STMT-R"])
        # A failed attempt is a present research record, not a successful proof.
        attempt = next(entry for entry in report["issues"][0]["requirements"] if entry["kind"] == "attempts")
        self.assertEqual(attempt["detail"], "failed")

    def test_malformed_contracts_do_not_count_as_delivered(self):
        bodies = [
            "results: RESULT-1",  # required brackets
            "results: [RESULT-1]\nresults: [RESULT-1]",  # duplicate field
            "unknown: [THING]",
            "statements: [STMT-P: magic]",
            "results: [RESULT-1, RESULT-1]",
            "statements: [STMT-P: closed, STMT-P: proved]",
            "results: []",
        ]
        items = [issue(index + 1, acceptance(body)) for index, body in enumerate(bodies)]
        items.append(issue(20, acceptance("results: [RESULT-1]"),
                           comments=[{"body": acceptance("attempts: [ATTEMPT-1]")}]))
        report = analyze_issues(items, records(), {"STMT-P": "proved"})
        self.assertEqual(report["summary"]["malformed"], 8)
        self.assertTrue(all(entry["errors"] for entry in report["issues"]))

    def test_comment_contract_and_reverse_index_are_deterministic(self):
        items = [
            issue(12, "Prose only", comments=[{"body": acceptance("statements: [STMT-Q: sourced]") }]),
            issue(4, acceptance("results: [RESULT-1]\nstatements: [STMT-Q: sourced]")),
        ]
        report = analyze_issues(items, records(), {})
        self.assertEqual([entry["number"] for entry in report["issues"]], [4, 12])
        self.assertEqual(issues_for_id(report, "STMT-Q"), [4, 12])
        self.assertEqual(issues_for_id(report, "RESULT-1"), [4])
        self.assertEqual(issues_for_id(report, "STMT-NOT-REFERENCED"), [])

    def test_statuses_do_not_confuse_proof_with_closed_or_sourced(self):
        items = [issue(7, acceptance("statements: [STMT-P: proved, STMT-Q: closed, STMT-R: sourced]"))]
        data = records()
        report = analyze_issues(items, data, {"STMT-P": "via_transcription", "STMT-Q": "self_evident"})
        requirements = report["issues"][0]["requirements"]
        self.assertEqual([(r["id"], r["met"]) for r in requirements],
                         [("STMT-P", False), ("STMT-Q", True), ("STMT-R", False)])

    def test_theorem_requires_registered_solution_and_a_matching_source_declaration(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / "Demo/Solution.lean"
            path.parent.mkdir(parents=True)
            path.write_text("namespace TruthCore.Demo\ntheorem proof : True := by trivial\nend TruthCore.Demo\n",
                            encoding="utf-8")
            data = records()
            data["results"][0]["solution_module"] = "Demo.Solution"
            issues = [issue(1, acceptance("theorems: [TruthCore.Demo.proof]"))]
            self.assertEqual(analyze_issues(issues, data, {}, root=root)["issues"][0]["status"], "delivered")
            path.write_text("namespace TruthCore.Demo\ntheorem somethingElse : True := by trivial\n",
                            encoding="utf-8")
            self.assertEqual(analyze_issues(issues, data, {}, root=root)["issues"][0]["status"], "missing")
            path.write_text("/-\ntheorem proof : True := by trivial\n-/\n", encoding="utf-8")
            self.assertEqual(analyze_issues(issues, data, {}, root=root)["issues"][0]["status"], "missing")
            # Same short name in another namespace, or a primed name, is not the registered theorem.
            for wrong in ("namespace TruthCore.Other\ntheorem proof : True := by trivial\nend TruthCore.Other\n",
                          "namespace TruthCore.Demo\ntheorem proof' : True := by trivial\nend TruthCore.Demo\n"):
                path.write_text(wrong, encoding="utf-8")
                self.assertEqual(analyze_issues(issues, data, {}, root=root)["issues"][0]["status"], "missing")
            path.write_text("namespace TruthCore\nsection\nnamespace Demo\ntheorem proof : True := by trivial\n"
                            "end Demo\nend\nend TruthCore\n", encoding="utf-8")
            self.assertEqual(analyze_issues(issues, data, {}, root=root)["issues"][0]["status"], "delivered")

    def test_crlf_contracts_are_found_and_counted_as_duplicates(self):
        crlf = acceptance("results: [RESULT-1]").replace("\n", "\r\n")
        report = analyze_issues([issue(1, crlf)], records(), {})
        self.assertEqual(report["issues"][0]["status"], "delivered")
        mixed = issue(2, acceptance("results: [RESULT-1]"),
                      comments=[{"body": acceptance("results: [RESULT-PENDING]").replace("\n", "\r\n")}])
        self.assertEqual(analyze_issues([mixed], records(), {})["issues"][0]["status"], "malformed")

    def test_offline_cli_reads_gh_shape_and_never_mutates_snapshot(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "issues.json"
            issues = [issue(3, acceptance("results: [RESULT-1]"))]
            path.write_text(json.dumps(issues), encoding="utf-8")
            before = path.read_bytes()
            stdout = io.StringIO()
            with contextlib.redirect_stdout(stdout):
                code = corpus.main_with(["issues", "--from", str(path), "--json"])
            self.assertEqual(code, 0)
            report = json.loads(stdout.getvalue())
            self.assertEqual(report["issues"][0]["number"], 3)
            self.assertEqual(path.read_bytes(), before)


if __name__ == "__main__":
    unittest.main()
