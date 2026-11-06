import TruthCore.Causality.ComposerTemporalDefinitionFork

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
  sorry

end TruthCore.Results.Causality.ComposerTemporalDefinitions.PastSelfCountermodel
