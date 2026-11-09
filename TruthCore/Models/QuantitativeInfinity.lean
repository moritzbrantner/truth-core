module

public import Mathlib.Order.Bounds.Basic

/-! INFINITE_2: analyst interpretation of unbounded quantity OR extension.
Magnitude domains and the represented measurements are explicit inputs. This
neither selects a real-line geometry nor identifies infinity with cardinality,
absence of a greatest element, or unreceived subsistent being. -/

@[expose] public section

namespace TruthCore.Models.QuantitativeInfinity

/-- `quantity` and `extension` list the represented magnitudes of one subject,
including its parts or stages when those are selected by the interpretation.
Each preorder compares magnitudes in its own units; a bound ranges over the
whole ambient magnitude domain, not just attained measurements. Reflexivity
and transitivity come from `Preorder`; totality, addition, a metric and a
measure are not assumed. Actual versus potentially attained measurements is
not decided by this interface: an application must state which it represents.
No field asserts unboundedness or connects magnitudes to divine perfection. -/
structure Magnitudes (Quantity : Type u) (Extension : Type v) where
  quantity : Set Quantity
  extension : Set Extension

/-- A represented quantity family OR extension family has no upper bound in
its respective ambient ordered magnitude domain. This is the full disjunction,
not a chosen coordinate, cardinal infinity, or a potential-growth assertion. -/
def IsInfinite {Q : Type u} {E : Type v}
    [Preorder Q] [Preorder E] (m : Magnitudes Q E) : Prop :=
  ¬ BddAbove m.quantity ∨ ¬ BddAbove m.extension

private theorem naturals_unbounded : ¬ BddAbove (Set.univ : Set ℕ) := by
  intro ⟨b, hb⟩
  exact Nat.not_succ_le_self b (hb (Set.mem_univ (b + 1)))

/-- Quantity alone can supply the disjunction, with extension bounded. -/
theorem quantity_control :
    IsInfinite (⟨Set.univ, {0}⟩ : Magnitudes ℕ ℕ) ∧
    BddAbove ({0} : Set ℕ) := by
  exact ⟨Or.inl naturals_unbounded, ⟨0, by simp⟩⟩

/-- Extension alone can supply the disjunction, with quantity bounded. -/
theorem extension_control :
    IsInfinite (⟨{0}, Set.univ⟩ : Magnitudes ℕ ℕ) ∧
    BddAbove ({0} : Set ℕ) := by
  exact ⟨Or.inr naturals_unbounded, ⟨0, by simp⟩⟩

/-- A nonempty bounded interpretation falsifies the sense. These natural
number fixtures are controls, not a restriction of its general definition. -/
theorem bounded_control :
    ¬ IsInfinite (⟨{0}, {0}⟩ : Magnitudes ℕ ℕ) := by
  intro h
  have hb : BddAbove ({0} : Set ℕ) := ⟨0, by simp⟩
  exact h.elim (fun hn => hn hb) (fun hn => hn hb)

end TruthCore.Models.QuantitativeInfinity
