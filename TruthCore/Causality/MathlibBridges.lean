import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Logic.Relation
import TruthCore.Causality.EssentialPower
import TruthCore.Causality.Supertasks

/-!
# Mathlib names for hand-rolled causality and supertask notions

Several notions in `TruthCore.Causality` predate the Mathlib dependency and are
fixed by frozen Challenges (AGENTS.md invariant 12), so they stay as defined.
This module proves that each coincides with the Mathlib notion it rolls by
hand, so later work can use Mathlib's library about them without restating
them. The vocabulary modules themselves stay Mathlib-free, which keeps their
results zero-axiom.

None of these lemmas is a corpus result; they bind no statement.
-/

namespace TruthCore.Causality

open Filter

/-- `StableAtLimit` is Mathlib's "eventually, along `atTop`": the output
eventually equals the terminal value. -/
theorem stableAtLimit_iff_eventually (output : Nat → Bool) (terminal : Bool) :
    StableAtLimit output terminal ↔ ∀ᶠ n in atTop, output n = terminal :=
  eventually_atTop.symm

/-- A `FiniteCausalPath` from `x` to `z` is a reflexive-transitive chain of
upstream links, i.e. Mathlib's `Relation.ReflTransGen` of the flipped cause
relation. -/
theorem finiteCausalPath_iff_reflTransGen {Being : Type}
    (causesAsCaused : Being → Being → Prop) (x z : Being) :
    FiniteCausalPath causesAsCaused x z ↔
      Relation.ReflTransGen (fun a b => causesAsCaused b a) x z := by
  constructor
  · intro path
    induction path with
    | same x => exact .refl
    | link hLink _ ih => exact Relation.ReflTransGen.head hLink ih
  · intro chain
    induction chain using Relation.ReflTransGen.head_induction_on with
    | refl => exact .same _
    | head hLink _ ih => exact .link hLink ih

/-- The unit-cost partial sum of `n` stages is `n`. -/
theorem unitCostPartialSum_eq (n : Nat) : UnitCostPartialSum n = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [UnitCostPartialSum, ih]

end TruthCore.Causality
