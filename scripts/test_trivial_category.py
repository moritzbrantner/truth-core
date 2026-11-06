#!/usr/bin/env python3
"""Tests for the constant category-predicate warning (#1103). Run with:

    python3 -m unittest discover -s scripts -p 'test_*.py'
"""

from __future__ import annotations

import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import corpus  # noqa: E402


def warnings_for(source: str) -> list[str]:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        (root / "TruthCore").mkdir()
        (root / "TruthCore" / "M.lean").write_text(source, encoding="utf-8")
        return corpus.trivial_category_warnings(root)


class TrivialCategoryTest(unittest.TestCase):
    def test_constant_field_is_reported(self) -> None:
        found = warnings_for("def p : Profile B where\n  concrete := fun _ => True\n")
        self.assertEqual(len(found), 1)
        self.assertIn("M.lean:2", found[0])
        self.assertIn("concrete is constantly True", found[0])

    def test_constant_definitions_are_reported(self) -> None:
        self.assertEqual(len(warnings_for("def Concrete (_ : Being) : Prop := True\n")), 1)
        self.assertEqual(len(warnings_for("def alternatingConcrete : ExistsAt Bool Bool := fun _ _ => False\n")), 1)
        self.assertEqual(len(warnings_for("  abstract := fun _ => False\n")), 1)

    def test_declared_or_nonconstant_sites_pass(self) -> None:
        self.assertEqual(warnings_for("  concrete := fun _ => True  -- category-constant: intended (fixture)\n"), [])
        self.assertEqual(
            warnings_for("-- category-constant: intended (no abstracta)\n  abstract := fun _ => False\n"), []
        )
        self.assertEqual(warnings_for("  concrete := fun x => x = c\n"), [])
        self.assertEqual(warnings_for("  powerConcrete := fun _ _ _ => True.intro\n"), [])
        self.assertEqual(warnings_for("def abstractMaking : Making := fun _ _ _ => True\n"), [])

    def test_named_binders_and_multiline_are_reported(self) -> None:
        self.assertEqual(len(warnings_for("  concrete := fun x => True\n")), 1)
        self.assertEqual(len(warnings_for("  concrete := fun (x : B) => True\n")), 1)
        found = warnings_for("  concrete := fun _ =>\n    True\n")
        self.assertEqual(len(found), 1)
        self.assertIn("M.lean:1", found[0])

    def test_literal_prefix_of_larger_body_is_not_constant(self) -> None:
        self.assertEqual(warnings_for("  concrete := fun _x => True ∧ _x = c\n"), [])
        self.assertEqual(warnings_for("  concrete := fun _x => False ∨ _x = c\n"), [])

    def test_marker_does_not_carry_to_next_declaration(self) -> None:
        source = (
            "  concrete := fun _ => True  -- category-constant: intended (fixture)\n"
            "  abstract := fun _ => False\n"
        )
        found = warnings_for(source)
        self.assertEqual(len(found), 1)
        self.assertIn("abstract is constantly False", found[0])

    def test_block_comments_are_not_scanned(self) -> None:
        self.assertEqual(warnings_for("/- example:\n  concrete := fun _ => True\n-/\n"), [])
        self.assertEqual(warnings_for("/-- doc /- nested -/ concrete := fun _ => True -/\ndef x := 1\n"), [])


if __name__ == "__main__":
    unittest.main()
