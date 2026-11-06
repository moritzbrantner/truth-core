module

public import TruthCore.Causality.ComposerTemporalDefinitionFork

@[expose] public section
namespace TruthCore.Results.Causality.ComposerTemporalDefinitions.Boundaries

open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article7Uniting
open TruthCore.Causality.ComposerTemporalDefinitionFork
universe u v w

/-- Frozen analyst obligation; interpretation applicability remains open. -/
theorem boundaries  :
    (TemporalDefinition pastBuilder ∧ TemporalComposer pastBuilder ∧
      AllTimeNoSelf pastBuilder ∧ ¬ CurrentComposer pastBuilder ∧ ¬ CurrentDefinition pastBuilder) ∧
    (TemporalComposer pastSelf ∧ CurrentNoSelf pastSelf ∧ ¬ AllTimeNoSelf pastSelf) ∧
    (CurrentDefinition overlap ∧ TemporalDefinition overlap ∧ CurrentComposer overlap) ∧
    Other remainder ∧
    (UniterPersistence localOnly ∧ ¬ GlobalPersistence localOnly) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro c x r
    constructor
    · intro h; exact ⟨false, rfl, h⟩
    · intro h; obtain ⟨t, ht⟩ := h; exact ht.2
  · intro c a b x h; exact ⟨(), false, rfl, h⟩
  · intro t x r h
    exact Bool.noConfusion (h.2.1.symm.trans h.2.2)
  · intro h
    obtain ⟨r, hr⟩ := h false false true true ⟨rfl, rfl⟩
    exact Bool.noConfusion hr.1
  · intro h
    have hh := (h false true ()).mp ⟨rfl, rfl⟩
    exact Bool.noConfusion hh.1
  · intro c a b x h; exact ⟨(), false, rfl, h⟩
  · intro x r h; exact Bool.noConfusion h.1
  · intro h; exact h false false () ⟨rfl, rfl⟩
  · intro c x r; exact Iff.rfl
  · intro c x r
    constructor
    · intro h; exact ⟨true, h⟩
    · intro h; obtain ⟨t, ht⟩ := h; exact ht
  · intro c a b x h; exact ⟨(), h⟩
  · intro h; exact (h () () ()).mp True.intro
  · intro h
    obtain ⟨t, ht⟩ := (h () () ()).mp True.intro
    exact ht
  · intro c a b x h _; exact ⟨(), Or.inl h⟩
  · intro h
    have hh := h true false () ⟨false, Or.inr ⟨rfl, rfl, rfl⟩⟩
    cases hh with
    | inl h => exact Bool.noConfusion h.1
    | inr h => exact Bool.noConfusion h.1


end TruthCore.Results.Causality.ComposerTemporalDefinitions.Boundaries
