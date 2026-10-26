#!/usr/bin/env python3
"""Tests for the Comparator axiom policy (docs/axiom-policy.md). Run with:

    python3 -m unittest discover -s scripts -p 'test_*.py'
"""

from __future__ import annotations

import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent))

import corpus  # noqa: E402

MATHLIB_AXIOMS = ["propext", "Classical.choice", "Quot.sound"]


class AxiomPolicyTest(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        root = Path(self.tmp.name)
        (root / "TruthCore" / "R").mkdir(parents=True)
        (root / "TruthCore" / "Vocab.lean").write_text(
            "import Mathlib.Analysis.SpecificLimits.Basic\n"
        )
        (root / "TruthCore" / "Plain.lean").write_text("namespace X\nend X\n")
        (root / "TruthCore" / "R" / "Uses.lean").write_text("import TruthCore.Vocab\n")
        (root / "TruthCore" / "R" / "Core.lean").write_text("import TruthCore.Plain\n")
        patcher = mock.patch.object(corpus, "ROOT", root)
        patcher.start()
        self.addCleanup(patcher.stop)
        self.addCleanup(self.tmp.cleanup)

    def error(self, solution: str, axioms: object) -> str | None:
        return corpus.permitted_axioms_error(
            {"solution_module": solution, "permitted_axioms": axioms}
        )

    def test_zero_axioms_always_allowed(self) -> None:
        self.assertIsNone(self.error("TruthCore.R.Core", []))
        self.assertIsNone(self.error("TruthCore.R.Uses", []))

    def test_mathlib_solution_may_permit_exactly_the_three(self) -> None:
        self.assertIsNone(self.error("TruthCore.R.Uses", MATHLIB_AXIOMS))
        self.assertIsNone(self.error("TruthCore.R.Uses", list(reversed(MATHLIB_AXIOMS))))

    def test_core_solution_stays_zero_axiom(self) -> None:
        self.assertIn("zero-axiom", self.error("TruthCore.R.Core", MATHLIB_AXIOMS))

    def test_other_axioms_rejected(self) -> None:
        for axioms in (
            ["propext"],
            MATHLIB_AXIOMS + ["Lean.trustCompiler"],
            MATHLIB_AXIOMS + ["TruthCore.myAxiom"],
            None,
        ):
            with self.subTest(axioms=axioms):
                self.assertIn("must be []", self.error("TruthCore.R.Uses", axioms))


if __name__ == "__main__":
    unittest.main()
