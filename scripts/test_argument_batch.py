#!/usr/bin/env python3
"""Tests for scripts/argument_batch.py (owner decision 2026-11-07)."""

from __future__ import annotations

import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import argument_batch  # noqa: E402

SOLUTION = """module

public import TruthCore.Foo

@[expose] public section

namespace TruthCore.Results.Bar
open TruthCore.Foo

/-- Helper, omitted from the Challenge. -/
theorem helper : True := trivial

/-- The advertised theorem. -/
theorem main (p : Prop) (hp : p) :
    p ∧ True :=
  ⟨hp, helper⟩

end TruthCore.Results.Bar
"""


class ChallengeTextTest(unittest.TestCase):
    def test_keeps_named_signatures_with_sorry_and_drops_helpers(self) -> None:
        text = argument_batch.challenge_text(SOLUTION, ["main"])
        self.assertIn("import TruthCore.Foo", text)
        self.assertNotIn("public import", text)
        self.assertNotIn("module", text.splitlines()[0])
        self.assertIn("theorem main (p : Prop) (hp : p) :\n    p ∧ True := by\n  sorry", text)
        self.assertNotIn("helper", text)
        self.assertIn("open TruthCore.Foo", text)
        self.assertIn("end TruthCore.Results.Bar", text)

    def test_missing_theorem_is_an_error(self) -> None:
        with self.assertRaises(SystemExit):
            argument_batch.challenge_text(SOLUTION, ["absent"])


class SlugTest(unittest.TestCase):
    def test_slug_drops_prefix(self) -> None:
        self.assertEqual(argument_batch.slug("STMT-FOO-BAR"), "foo-bar")
        self.assertEqual(argument_batch.slug("FOO-FROM-BAR"), "foo-from-bar")


if __name__ == "__main__":
    unittest.main()
