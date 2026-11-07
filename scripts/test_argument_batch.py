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

/-! A module docstring
that spans lines and mentions
end of things, section headings and theorem names. -/

namespace TruthCore.Results.Bar
open TruthCore.Foo

namespace Control
def witness : Prop := True
end Control

section Helpers
/-- Helper, omitted from the Challenge. -/
theorem helper : True := trivial

/-- The advertised theorem. -/
theorem main (p : Prop) (hp : p) :
    p ∧ True :=
  ⟨hp, helper⟩
end Helpers

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
        self.assertIn("namespace Control", text)
        self.assertIn("end Control", text)
        self.assertNotIn("end Helpers", text)
        self.assertIn("end of things, section headings and theorem names. -/", text)

    def test_missing_theorem_is_an_error(self) -> None:
        with self.assertRaises(SystemExit):
            argument_batch.challenge_text(SOLUTION, ["absent"])


class HandlesTest(unittest.TestCase):
    """Spec handles resolve to uuids; new records get uuid4 ids and plain labels."""

    def test_legacy_handle_resolves_and_new_records_need_a_plain_label(self) -> None:
        from corpus_ids import is_uuid, legacy_uuid

        handles = argument_batch.Handles()
        self.assertEqual(handles.get("statement", "STMT-EXCLUDED-MIDDLE"),
                         legacy_uuid("statement", "STMT-EXCLUDED-MIDDLE"))
        minted = handles.get("statement", "brand new handle", "A brand new proposition for the test")
        self.assertTrue(is_uuid(minted))
        self.assertNotEqual(minted, legacy_uuid("statement", "brand new handle"))
        self.assertEqual(handles.ref("statement", "brand new handle"), minted)
        with self.assertRaises(SystemExit):
            handles.get("statement", "STMT-NOT-A-RECORD-YET")


if __name__ == "__main__":
    unittest.main()
