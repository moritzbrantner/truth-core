module

public import TruthCore.Causality.ComposerTemporalDefinitionFork

@[expose] public section
namespace TruthCore.Results.Causality.ComposerTemporalDefinitions.PastSelfCountermodel
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article7Uniting
open TruthCore.Causality.ComposerTemporalDefinitionFork

/-- The historical route fails under a selected-time-only self-causation ban,
 even with the same other three composition inputs and a nonempty composite. -/
theorem pastSelfCountermodel :
    TemporalComposer pastSelf ∧ CurrentNoSelf pastSelf ∧
    CompositeHasTwoDistinctComponentsReading selfComposite selfComponent ∧
    DiverseUnitedOnlyThroughUnitingCauseReading selfComponent pastSelf.Unites ∧
    UnitingCauseCausesBeingReading pastSelf.Unites selfCauses () ∧
    selfComposite false ∧
    ¬ CompositeConclusion pastSelf selfComposite selfCauses () := by
  refine ⟨?_, ?_, ?_, ?_, ?_, True.intro, ?_⟩
  · intro c a b x h; exact ⟨(), false, rfl, h⟩
  · intro x r h; exact Bool.noConfusion h.1
  · intro x _; exact ⟨false, true, True.intro, True.intro, Bool.noConfusion⟩
  · intro x a b _ _ _; exact ⟨x, rfl⟩
  · intro c a b x h; exact h
  · intro h
    obtain ⟨c, hn, he⟩ := h false True.intro
    exact hn he


end TruthCore.Results.Causality.ComposerTemporalDefinitions.PastSelfCountermodel
