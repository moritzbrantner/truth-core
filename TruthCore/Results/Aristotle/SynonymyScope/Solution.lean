import TruthCore.Greek.Aristotle.SynonymousCause
namespace TruthCore.Results.Aristotle.SynonymyScope
open TruthCore.Greek.Aristotle.Metaphysics
/-- The finite typed interpretation witnesses both relevant causal cases. -/
theorem synonymyScopeControl : SynonymyScopeControl := by
  refine ⟨fun c x _ => (c = 0 ∧ x = 1) ∨ (c = 1 ∧ x = 2),
    fun _ c x => c = 0 ∧ x = 1,
    fun c _ s => (c = 0 ∧ s = false) ∨ (c = 1 ∧ s = false) ∨ (c = 2 ∧ s = true), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c x r _ hc hs
    rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
    · rcases hs with ⟨s, h1, h2⟩
      cases s <;> simp at h1 h2
  · intro h
    have bad := h 1 2 () (by decide) (Or.inr ⟨rfl, rfl⟩)
    exact (by decide : ¬ ((1 : Fin 3) = 0 ∧ (2 : Fin 3) = 1)) bad
  · exact Or.inl ⟨rfl, rfl⟩
  · exact ⟨false, Or.inl ⟨rfl, rfl⟩, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
  · exact ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩
  · rintro ⟨s, h1, h2⟩
    cases s <;> simp at h1 h2
  · decide
end TruthCore.Results.Aristotle.SynonymyScope
