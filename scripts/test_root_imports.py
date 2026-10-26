import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import root_imports as ri  # noqa: E402

AREAS = ("Greek/NewTestament", "Results/Case/Catholicism/StageThree")


def touch(root: Path, relative: str, text: str = "theorem t : True := trivial\n") -> None:
    path = root / relative
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text)


class AreaTest(unittest.TestCase):
    def test_default_areas(self):
        self.assertEqual(ri.area_of(Path("Latin/Aquinas/X.lean"), AREAS), "Latin")
        self.assertEqual(ri.area_of(Path("Greek/X.lean"), AREAS), "Greek")
        self.assertEqual(ri.area_of(Path("Results/Aquinas/R/Solution.lean"), AREAS), "Results/Aquinas")
        self.assertEqual(ri.area_of(Path("Results/X.lean"), AREAS), "Results")

    def test_longest_configured_prefix_wins(self):
        self.assertEqual(ri.area_of(Path("Greek/NewTestament/Mark.lean"), AREAS), "Greek/NewTestament")
        self.assertEqual(
            ri.area_of(Path("Results/Case/Catholicism/StageThree/R/Solution.lean"), AREAS),
            "Results/Case/Catholicism/StageThree",
        )
        self.assertEqual(ri.area_of(Path("Results/Case/Catholicism/R/Solution.lean"), AREAS), "Results/Case")

    def test_prefix_matches_whole_directories_only(self):
        self.assertEqual(ri.area_of(Path("Greek/NewTestamentNotes/X.lean"), AREAS), "Greek")

    def test_top_level_module_is_rejected(self):
        with self.assertRaises(ri.RootImportsError):
            ri.area_of(Path("Loose.lean"), AREAS)


class GenerateTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        touch(self.root, "TruthCore/Latin/B.lean")
        touch(self.root, "TruthCore/Latin/A/C.lean")
        touch(self.root, "TruthCore/Greek/NewTestament/Mark.lean")
        touch(self.root, "TruthCore/Results/Case/Catholicism/R/Solution.lean")
        touch(self.root, "TruthCore/Results/Case/Catholicism/R/Challenge.lean")

    def tearDown(self):
        self.tmp.cleanup()

    def test_write_then_check_is_clean(self):
        self.assertTrue(ri.check(self.root, AREAS))
        ri.write(self.root, AREAS)
        self.assertEqual(ri.check(self.root, AREAS), [])
        self.assertEqual(
            (self.root / "TruthCore.lean").read_text(),
            ri.HEADER
            + "import TruthCore.Imports.Greek.NewTestament\n"
            + "import TruthCore.Imports.Latin\n"
            + "import TruthCore.Imports.Results.Case\n",
        )
        self.assertEqual(
            (self.root / "TruthCore/Imports/Latin.lean").read_text(),
            ri.HEADER + "import TruthCore.Latin.A.C\nimport TruthCore.Latin.B\n",
        )
        self.assertNotIn(
            "Challenge", (self.root / "TruthCore/Imports/Results/Case.lean").read_text()
        )

    def test_new_module_touches_only_its_aggregator(self):
        ri.write(self.root, AREAS)
        touch(self.root, "TruthCore/Latin/D.lean")
        changed, removed = ri.stale(self.root, AREAS)
        self.assertEqual(sorted(changed), ["TruthCore/Imports/Latin.lean"])
        self.assertEqual(removed, [])

    def test_emptied_area_is_removed(self):
        ri.write(self.root, AREAS)
        (self.root / "TruthCore/Greek/NewTestament/Mark.lean").unlink()
        report = ri.check(self.root, AREAS)
        self.assertTrue(any("Greek/NewTestament.lean" in line for line in report))
        ri.write(self.root, AREAS)
        self.assertFalse((self.root / "TruthCore/Imports/Greek").exists())
        self.assertEqual(ri.check(self.root, AREAS), [])

    def test_hand_edit_is_reported(self):
        ri.write(self.root, AREAS)
        path = self.root / "TruthCore/Imports/Latin.lean"
        path.write_text(path.read_text() + "import TruthCore.Extra\n")
        self.assertTrue(ri.check(self.root, AREAS))


if __name__ == "__main__":
    unittest.main()
