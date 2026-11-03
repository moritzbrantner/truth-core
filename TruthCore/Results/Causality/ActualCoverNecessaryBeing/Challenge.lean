import TruthCore.Causality.ActualCoverNecessaryBeing

namespace TruthCore.Results.Causality.ActualCoverNecessaryBeing
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Causality.ActualFusionNecessaryBeing
open TruthCore.Causality.ActualCoverNecessaryBeing
open TruthCore.Causality.NecessarilyUnderived (ActualReflexive)
open TruthCore.Explanation.ExistencePSR
open TruthCore.Explanation.WellFoundedSource (PopulatedAt)

/-- Six explicit inputs derive SOME bare actual necessary individual. Actual
coverage and cause-nonparthood replace fusion and full causal nonoverlap. -/
theorem fromPopulation {W B : Type} [PartialOrder B] (M : Model W B) (w : W)
    (hPopulation : PopulatedAt M w)
    (hCover : ConditionalActualCoverAt M.ontic w)
    (hReflexive : ActualReflexive M.ontic w)
    (hCausal : ActualNoNecessaryPartsHaveCausesAt M.ontic w)
    (hActual : CausesHaveActualEndpointsAt M.ontic w)
    (hNonpart : CauseNotPartOfEffectAt M.ontic w) : NecessaryBeing M.ontic w := by
  sorry

end TruthCore.Results.Causality.ActualCoverNecessaryBeing
