import TruthCore.Greek.Aristotle.SynonymousCause
namespace TruthCore.Results.Aristotle.SynonymyScope
open TruthCore.Greek.Aristotle.Metaphysics
/-- The finite typed interpretation witnesses both relevant causal cases. -/
theorem synonymyScopeControl : SynonymyScopeControl := by
  refine ⟨fun c x _ => (c = scopePoint0 ∧ x = scopePoint1) ∨ (c = scopePoint1 ∧ x = scopePoint2),
    fun _ c x => c = scopePoint0 ∧ x = scopePoint1,
    fun c _ s => (c = scopePoint0 ∧ s = false) ∨ (c = scopePoint1 ∧ s = false) ∨ (c = scopePoint2 ∧ s = true), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c x r _ hc hs
    rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
    · have noShared : ¬ ∃ s : Bool,
          ((scopePoint1 = scopePoint0 ∧ s = false) ∨ (scopePoint1 = scopePoint1 ∧ s = false) ∨ (scopePoint1 = scopePoint2 ∧ s = true)) ∧
          ((scopePoint2 = scopePoint0 ∧ s = false) ∨ (scopePoint2 = scopePoint1 ∧ s = false) ∨ (scopePoint2 = scopePoint2 ∧ s = true)) := by decide
      exact False.elim (noShared hs)
  · intro h
    have bad := h scopePoint1 scopePoint2 () (by decide) (Or.inr ⟨rfl, rfl⟩)
    exact (by decide : ¬ (scopePoint1 = scopePoint0 ∧ scopePoint2 = scopePoint1)) bad
  · exact Or.inl ⟨rfl, rfl⟩
  · exact ⟨false, Or.inl ⟨rfl, rfl⟩, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
  · exact ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩
  · decide
  · decide
end TruthCore.Results.Aristotle.SynonymyScope
