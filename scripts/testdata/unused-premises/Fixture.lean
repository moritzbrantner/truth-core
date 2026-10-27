/-
Fixture for `scripts/test_unused_premises.py` (#571). Compiled by the test as
module `TruthCore.UnusedPremisesFixture` (outside the library), then described
by `scripts/UnusedPremises.lean`. Each theorem's comment gives the expected
usage.
-/
set_option linter.unusedVariables false
namespace TruthCore.UnusedPremisesFixture

def Th (A B C : Prop) : Prop := A ∧ B ∧ C

theorem helper (A B : Prop) (ha : A) (hb : B) : A := ha

/-- `hb` unused. -/
theorem plain (A B : Prop) (ha : A) (hb : B) : A := ha

/-- `hb` passed to a helper that ignores it: unused. -/
theorem viaHelper (A B : Prop) (ha : A) (hb : B) : A := helper A B ha hb

/-- Only conjunct 2 used (`obtain` with `_`). -/
theorem obt (A B C : Prop) (h : Th A B C) : B := by
  obtain ⟨_, hb, _⟩ := h
  exact hb

/-- Only conjunct 3 used (projection). -/
theorem proj (A B C : Prop) (h : Th A B C) : C := h.2.2

/-- Only conjunct 1 used (`match` auxiliary). -/
theorem mtch (A B C : Prop) (h : Th A B C) : A := match h with | ⟨a, _, _⟩ => a

/-- `hb` only bound by an unused `have`: unused. -/
theorem haveUnused (A B : Prop) (ha : A) (hb : B) : A := by
  have _x := hb
  exact ha

/-- Both used. -/
theorem both (A B : Prop) (ha : A) (hb : A → B) : B := hb ha

end TruthCore.UnusedPremisesFixture
