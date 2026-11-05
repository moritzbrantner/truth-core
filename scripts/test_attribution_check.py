"""Tests for the pre-push attribution self-check (#989)."""

from __future__ import annotations

import tempfile
import unittest
from pathlib import Path
from unittest import mock

import attribution_check as ac

PASSAGE = {
    "id": "TEXT-1", "kind": None, "source_id": "SRC", "locator": "I q.9 a.1",
    "claim_locator_prefixes": ["I q.9 a.1"],
}
BIB = {
    "id": "BIB-1", "kind": "bibliographic_span", "source_id": "BOOK", "locator": "pp. 1-2",
    "claim_locator_prefixes": ["pp. 1"], "author": "A", "title": "T", "publisher": "P", "year": 2000,
    "isbn": "9780000000002", "pages": "1-2",
}
STATEMENT = {"id": "STMT-P", "paraphrase": "Whatever is changed is in potency."}
GOOD = "The passage states that whatever is changed in any way is in potency, which is the premise."


def claim(**extra) -> dict:
    return {"id": "C", "statement_id": "STMT-P", "source_id": "SRC", "locator": "I q.9 a.1 co.",
            "interpretation": "reading", **extra}


class ValidateAttributionTest(unittest.TestCase):
    def test_shape(self) -> None:
        ac.validate_attribution("c.json", claim())
        ac.validate_attribution("c.json", claim(attribution=GOOD))
        for bad in ("It is stated somewhere in the passage, I think.", "The passage states X.", 7):
            with self.subTest(bad=bad), self.assertRaisesRegex(ac.AttributionError, "attribution must be"):
                ac.validate_attribution("c.json", claim(attribution=bad))


class ReportTest(unittest.TestCase):
    def run_report(self, claims, cached_text: str | None = "Omne quod mutatur est in potentia."):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        cache = Path(directory.name)
        if cached_text is not None:
            (cache / "TEXT-1.txt").write_text(cached_text)
        passages = {"TEXT-1": (Path("p.json"), PASSAGE), "BIB-1": (Path("b.json"), BIB)}
        with (
            mock.patch.object(ac, "changed_claims", return_value=claims),
            mock.patch.object(ac.se, "passage_index", return_value=passages),
            mock.patch.object(ac.se, "load_json_dir", return_value=[(Path("s.json"), STATEMENT)]),
            mock.patch.object(ac.se, "CACHE", cache),
            mock.patch.object(ac, "ROOT", cache.parent),
            mock.patch.object(ac, "changed_paths", return_value=[]),
        ):
            return ac.report("origin/main", materialize=False, max_chars=0)

    def test_prints_premise_beside_passage_and_fails_without_attribution(self) -> None:
        text, problems = self.run_report([(claim(), "new claim")])
        self.assertIn("premise: Whatever is changed is in potency.", text)
        self.assertIn("Omne quod mutatur est in potentia.", text)
        self.assertIn("quantifier scope", text)
        self.assertIn("attribution: MISSING", text)
        self.assertEqual(problems, ["C: no `attribution` recorded"])

    def test_recorded_attribution_passes(self) -> None:
        text, problems = self.run_report([(claim(attribution=GOOD), "changed interpretation")])
        self.assertIn(f"attribution: {GOOD}", text)
        self.assertEqual(problems, [])

    def test_unread_passage_fails(self) -> None:
        _, problems = self.run_report([(claim(attribution=GOOD), "new claim")], cached_text=None)
        self.assertEqual(len(problems), 1)
        self.assertIn("text not read", problems[0])

    def test_bibliographic_claim_names_the_edition_and_needs_only_the_attribution(self) -> None:
        bib_claim = claim(source_id="BOOK", locator="pp. 1", witness="bibliographic", attribution=GOOD)
        text, problems = self.run_report([(bib_claim, "new claim")], cached_text=None)
        self.assertIn("read A, T", text)
        self.assertEqual(problems, [])

    def test_no_changed_claims(self) -> None:
        text, problems = self.run_report([])
        self.assertIn("no new or changed stating claim", text)
        self.assertEqual(problems, [])


class ChangedClaimsTest(unittest.TestCase):
    """Selection by stable ID, statement text and resolved passage (#998 review)."""

    def select(self, paths, base_files, head_files, claims=()):
        def read_at(revision, path):
            return (base_files if revision is not None else head_files).get(path)

        passages = {"TEXT-1": (Path("p.json"), PASSAGE)}
        with (
            mock.patch.object(ac, "changed_paths", return_value=paths),
            mock.patch.object(ac, "read_at", side_effect=read_at),
            mock.patch.object(ac.se, "load_json_dir", return_value=[(Path("c.json"), c) for c in claims]),
        ):
            return [(c["id"], reason) for c, reason in ac.changed_claims("origin/main", passages)]

    def test_moved_claim_file_is_compared_by_id(self) -> None:
        old, new = "corpus/claims/old.json", "corpus/claims/new.json"
        self.assertEqual(self.select([old, new], {old: claim()}, {new: claim()}), [])
        self.assertEqual(
            self.select([old, new], {old: claim()}, {new: claim(interpretation="broader")}),
            [("C", "changed interpretation")],
        )

    def test_renamed_statement_with_new_paraphrase_selects_its_claims(self) -> None:
        old, new = "corpus/statements/old.json", "corpus/statements/new.json"
        broadened = dict(STATEMENT, paraphrase="Whatever exists is in potency.")
        self.assertEqual(
            self.select([old, new], {old: STATEMENT}, {new: broadened}, claims=[claim()]),
            [("C", "statement STMT-P paraphrase changed")],
        )

    def test_changed_passage_selects_the_claims_resolving_to_it(self) -> None:
        manifest = "corpus/passages/p.json"
        head = {manifest: {"snapshot": {}, "passages": [{"id": "TEXT-1"}]}}
        self.assertEqual(
            self.select([manifest], {}, head, claims=[claim()]),
            [("C", "passage TEXT-1 changed")],
        )


if __name__ == "__main__":
    unittest.main()
