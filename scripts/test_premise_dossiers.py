#!/usr/bin/env python3
import copy
import unittest

import corpus
from premise_dossiers import dossier_index, validate_attempt


def attempt(**overrides):
    return {"id": "ATTEMPT-EXAMPLE", "statement_ids": ["P"], "date": "2026-10-26",
            "kind": "derivation", "outcome": "failed", "summary": "The proposed inference did not follow.",
            "evidence": ["RESULT", "CLAIM", "PR-413"], **overrides}


class AttemptValidationTests(unittest.TestCase):
    def test_accepts_local_evidence_and_canonical_pr_reference(self):
        validate_attempt(attempt(), {"P"}, {"RESULT", "CLAIM"})
        validate_attempt(attempt(evidence=[]), {"P"}, set())

    def test_rejects_unknown_references_and_malformed_fields(self):
        cases = [dict(statement_ids=[]), dict(statement_ids=["UNKNOWN"]), dict(statement_ids=["P", "P"]),
                 dict(date="2026-02-30"), dict(date="20261026"), dict(kind="proof"), dict(kind=[]),
                 dict(outcome="proved"), dict(outcome={}), dict(summary=" "), dict(evidence=["UNKNOWN"]),
                 dict(evidence=["PR-0"]), dict(evidence=["PR-413", "PR-413"]), dict(evidence=[{}]),
                 dict(outcome="blocked"), dict(blocker=""), dict(id="P")]
        for fields in cases:
            with self.subTest(fields=fields), self.assertRaises(ValueError):
                validate_attempt(attempt(**fields), {"P"}, {"RESULT", "CLAIM"})
        validate_attempt(attempt(outcome="blocked", blocker="A pinned witness is missing."), {"P"}, {"RESULT", "CLAIM"})


class DossierTests(unittest.TestCase):
    def setUp(self):
        self.data = {
            "statements": [{"id": sid, "paraphrase": sid} for sid in ["P", "I", "R"]],
            "claims": [{"id": "CLAIM", "statement_id": "P", "definition_ids": ["D1"]}],
            "definitions": [{"id": "D1"}, {"id": "D2"}],
            "disambiguations": [{"id": "DISAMB", "sense_definition_ids": ["D1", "D2"]}],
            "arguments": [{"id": "ARG", "premise_statement_ids": ["P"], "conclusion_statement_id": "R", "inference_ids": ["INF"]}],
            "inferences": [{"id": "INF", "input_statement_ids": ["P"], "output_statement_id": "I"}],
            "results": [{"id": "RESULT", "argument_id": "ARG", "description": "A countermodel in prose is not a registration."}],
            "relations": [], "attempts": [attempt(outcome="succeeded", kind="countermodel")],
        }
        self.report = corpus.frontier_report(self.data["statements"], self.data["arguments"], self.data["results"], [], root="R", claims=self.data["claims"])

    def test_successful_attempt_does_not_close_premise_and_route_membership_is_exact(self):
        before = copy.deepcopy(self.report)
        dossiers = dossier_index(self.data, self.report)
        self.assertEqual(before, self.report)
        self.assertIsNone(dossiers["P"]["closure"])
        self.assertFalse(dossiers["P"]["established"])
        self.assertTrue(dossiers["P"]["route_contributions"][0]["open_leaf"])
        self.assertEqual(dossiers["P"]["route_contributions"][0]["cost"], 1)
        self.assertFalse(dossiers["R"]["route_contributions"][0]["open_leaf"])
        self.assertEqual(dossiers["P"]["countermodel_attempt_ids"], ["ATTEMPT-EXAMPLE"])
        self.assertEqual(dossiers["R"]["countermodel_attempt_ids"], [])

    def test_inference_and_sense_links_are_included(self):
        dossiers = dossier_index(self.data, self.report)
        self.assertEqual(dossiers["I"]["argument_ids"], ["ARG"])
        self.assertEqual(dossiers["P"]["definition_ids"], ["D1", "D2"])
        self.assertEqual(dossiers["P"]["disambiguation_ids"], ["DISAMB"])

    def test_floor_basis_is_shown(self):
        from premise_dossiers import format_dossier
        self.data["statements"][0]["self_evident"] = {
            "basis": "observation", "justification_ids": ["CLAIM"], "sceptical_rival_ids": []}
        report = corpus.frontier_report(self.data["statements"], self.data["arguments"], self.data["results"], [],
                                        root="R", claims=self.data["claims"])
        dossier = dossier_index(self.data, report)["P"]
        self.assertEqual((dossier["closure"], dossier["floor"]["basis"], dossier["floor"]["met"]),
                         ("self_evident", "observation", True))
        self.data["definitions"] = [{"id": "D1", "definition": "d1"}, {"id": "D2", "definition": "d2"}]
        self.data["disambiguations"][0]["resolution"] = "r"
        self.data["claims"][0].update(source_id="S", locator="L", interpretation="i")
        self.data["arguments"][0]["meaning"] = "m"
        self.assertIn("Floor basis: observation (met); justification: CLAIM", format_dossier(dossier, self.data))

    def test_all_backfilled_attempts_bind_to_existing_records(self):
        data = {name: [record for _, record in corpus.load_dir(name)] for name in ("statements", "results", "claims", "attempts")}
        evidence = {entry["id"] for entry in data["results"] + data["claims"]}
        for entry in data["attempts"]:
            validate_attempt(entry, {entry["id"] for entry in data["statements"]}, evidence)

    def test_cli_unknown_statement_is_a_controlled_error(self):
        from contextlib import redirect_stderr
        from io import StringIO
        output = StringIO()
        with redirect_stderr(output):
            result = corpus.main_with(["dossier", "STMT-DOES-NOT-EXIST", "--json"])
        self.assertEqual(result, 2)
        self.assertIn("unknown statement", output.getvalue())


if __name__ == "__main__":
    unittest.main()
