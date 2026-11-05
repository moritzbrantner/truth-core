"""Offline tests for the module-system converter (docs/decisions/2026-11-05-01-lean-module-system.md)."""
from pathlib import Path
import tempfile
import unittest

import convert_to_module as conv


class ConvertTextTest(unittest.TestCase):
    def test_imports_docstring_and_section(self):
        text = "import TruthCore.A\nimport Mathlib.Order.Basic\n\n/-!\n# Title\n\nBody.\n-/\n\nnamespace X\ntheorem t : True := trivial\nend X\n"
        self.assertEqual(conv.convert_text(text), (
            "module\n\npublic import TruthCore.A\npublic import Mathlib.Order.Basic\n\n"
            "/-!\n# Title\n\nBody.\n-/\n\n@[expose] public section\n\n"
            "namespace X\ntheorem t : True := trivial\nend X\n"))

    def test_no_imports_and_leading_docstring(self):
        text = "/-! One line. -/\n\nnamespace X\nend X\n"
        self.assertEqual(conv.convert_text(text),
                         "module\n\n/-! One line. -/\n\n@[expose] public section\n\nnamespace X\nend X\n")

    def test_no_docstring(self):
        text = "import TruthCore.A\n\nnamespace X\nend X\n"
        self.assertEqual(conv.convert_text(text),
                         "module\n\npublic import TruthCore.A\n\n@[expose] public section\n\nnamespace X\nend X\n")

    def test_nested_comment_in_docstring(self):
        text = "/-!\nDoc /- inner\n-/\nstill doc.\n-/\n\ndef x := 1\n"
        self.assertEqual(conv.convert_text(text),
                         "module\n\n/-!\nDoc /- inner\n-/\nstill doc.\n-/\n\n@[expose] public section\n\ndef x := 1\n")
        for bad in ("/-! a /- b -/\n", "/-! doc -/ def x := 1\n"):
            with self.subTest(text=bad), self.assertRaises(conv.ConversionError):
                conv.convert_text(bad)

    def test_leading_comment_stays_above_module(self):
        text = "-- note\nimport TruthCore.A\n\ndef x := 1\n"
        self.assertTrue(conv.convert_text(text).startswith("-- note\nmodule\n\npublic import TruthCore.A\n"))

    def test_refusals(self):
        for text in ("module\n\npublic import A\n", "-- c\nmodule\n",
                     "import A -- why\n", "prelude\nimport A\n", "import A\ndef x := 1\nimport B\n",
                     "/-! open\n"):
            with self.subTest(text=text), self.assertRaises(conv.ConversionError):
                conv.convert_text(text)

    def test_is_module_skips_comments(self):
        self.assertTrue(conv.is_module_text("/- c -/\n-- d\nmodule\n"))
        self.assertFalse(conv.is_module_text("/-! module -/\nimport A\n"))


class GraphTest(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.root = Path(tmp.name)
        files = {
            "TruthCore.lean": "import TruthCore.Imports.All\n",
            "TruthCore/Imports/All.lean": "import TruthCore.A\nimport TruthCore.B\n",
            "TruthCore/A.lean": "namespace A\nend A\n",
            "TruthCore/B.lean": "import TruthCore.A\n\ndef b := 1\n",
            "TruthCore/T.lean": "import Mathlib.Tactic\n",
            "TruthCore/U.lean": "import TruthCore.T\n",
            "TruthCore/R/Challenge.lean": "import TruthCore.B\n",
            "TruthCore/R/Solution.lean": "import TruthCore.B\n",
            "TruthCore/M.lean": "module\n\npublic import TruthCore.A\n",
        }
        for rel, text in files.items():
            path = self.root / rel
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)

    def test_levels_and_selection(self):
        graph = conv.Graph(self.root)
        self.assertEqual(graph.level("TruthCore.A"), 0)
        self.assertEqual(graph.level("TruthCore.R.Solution"), 2)
        selected, blocked = graph.select(0)
        self.assertEqual(selected, ["TruthCore.A"])
        self.assertIn("TruthCore.T", blocked)
        selected, blocked = graph.select(None)
        self.assertEqual(selected, ["TruthCore.A", "TruthCore.B", "TruthCore.R.Solution"])
        self.assertEqual(set(blocked), {"TruthCore.T", "TruthCore.U"})
        # Challenges, aggregators and existing modules are never candidates.
        self.assertNotIn("TruthCore.R.Challenge", selected + list(blocked))
        self.assertNotIn("TruthCore.Imports.All", selected + list(blocked))
        self.assertNotIn("TruthCore.M", selected + list(blocked))

    def test_select_excludes_files_whose_imports_stay_ordinary(self):
        graph = conv.Graph(self.root)
        self.assertEqual(graph.blocker("TruthCore.B", set()), "imports non-module TruthCore.A")
        self.assertIsNone(graph.blocker("TruthCore.B", {"TruthCore.A"}))
        self.assertIsNotNone(graph.blocker("TruthCore.R.Challenge", {"TruthCore.B"}))


if __name__ == "__main__":
    unittest.main()
