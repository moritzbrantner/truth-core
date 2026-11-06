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
            warnings_for("-- category-constant: intended (no abstracta)\n\n  abstract := fun _ => False\n"), []
        )
        self.assertEqual(warnings_for("  concrete := fun x => x = c\n"), [])
        self.assertEqual(warnings_for("  powerConcrete := fun _ _ _ => True.intro\n"), [])
        self.assertEqual(warnings_for("def abstractMaking : Making := fun _ _ _ => True\n"), [])


if __name__ == "__main__":
    unittest.main()
