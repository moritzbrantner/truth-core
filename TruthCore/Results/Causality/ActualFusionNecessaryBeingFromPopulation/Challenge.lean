import TruthCore.Causality.ActualFusionNecessaryBeing
import TruthCore.Explanation.WellFoundedSource

namespace TruthCore.Results.Causality.ActualFusionNecessaryBeingFromPopulation
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Explanation.ExistencePSR
open TruthCore.Explanation.WellFoundedSource (PopulatedAt)
open TruthCore.Causality.ActualFusionNecessaryBeing

/-- Existing actual population plus conditional selected-family fusion and
four part/causal policies yield bare NE. The Model's explains field is unused;
no PSR, quality, actual wholly-contingent population or sum is presupposed. -/
theorem necessaryBeing {W B : Type} [PartialOrder B] (M : Model W B) (w : W)
    (hPopulation : PopulatedAt M w)
    (hFusion : ConditionalActualFusionAt M.ontic w)
    (hParts : ActualPartsExistAt M.ontic w)
    (hCausal : ActualNoNecessaryPartsHaveCausesAt M.ontic w)
    (hActual : CausesHaveActualEndpointsAt M.ontic w)
    (hNonoverlap : CauseEffectNonoverlapAt M.ontic w) :
    NecessaryBeing M.ontic w := by
  sorry

end TruthCore.Results.Causality.ActualFusionNecessaryBeingFromPopulation
