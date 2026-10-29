import TruthCore.Greek.Aristotle.SynonymousCauseAtLeast
namespace TruthCore.Results.Aristotle.SynonymyTie
open TruthCore.Greek.Aristotle.Metaphysics
/-- A same-account causal tie separates at-least and strict readings. -/
theorem synonymyTieControl : SynonymousCauseTieControl := by
  refine ⟨fun c x _ => c = false ∧ x = true, fun _ _ _ => True,
    fun _ _ _ => False, fun _ _ _ => True, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro _ _ _ _ _ _; trivial
  · intro h
    exact h false true () (by decide) ⟨rfl, rfl⟩ ⟨(), trivial, trivial⟩
  · exact ⟨rfl, rfl⟩
  · trivial
  · trivial
  · trivial
  · trivial
  · exact id
end TruthCore.Results.Aristotle.SynonymyTie
