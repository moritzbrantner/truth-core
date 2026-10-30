import TruthCore.Greek.Aristotle.SynonymousCauseAtLeast
namespace TruthCore.Results.Aristotle.SynonymyTie
open TruthCore.Greek.Aristotle.Metaphysics
/-- A same-account causal tie separates at-least and strict readings. -/
theorem synonymyTieControl : SynonymousCauseTieControl := by
  let degree : Bool → Nat := fun _ => 0
  refine ⟨fun c x _ => c = false ∧ x = true, fun _ c x => degree x ≤ degree c,
    fun _ c x => degree x < degree c, fun _ _ _ => True, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro _ _ _ _ _ _; exact Nat.le_refl 0
  · intro h
    exact Nat.not_lt_zero 0 (h false true () (by decide) ⟨rfl, rfl⟩ ⟨(), trivial, trivial⟩)
  · exact ⟨rfl, rfl⟩
  · trivial
  · trivial
  · trivial
  · trivial
  · exact Nat.not_lt_zero 0
end TruthCore.Results.Aristotle.SynonymyTie
