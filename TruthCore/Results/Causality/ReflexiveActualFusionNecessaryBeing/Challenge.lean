import TruthCore.Causality.ActualFusionNecessaryBeing
import TruthCore.Causality.NecessarilyUnderived
import TruthCore.Explanation.WellFoundedSource

namespace TruthCore.Results.Causality.ReflexiveActualFusionNecessaryBeing
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Causality.ActualFusionNecessaryBeing
open TruthCore.Causality.NecessarilyUnderived (ActualReflexive)
open TruthCore.Explanation.ExistencePSR
open TruthCore.Explanation.WellFoundedSource (PopulatedAt)

/-- Replace actual-part existence by selected-world reflexivity, with the
other four registered inputs unchanged. Output is SOME bare actual NE. -/
theorem necessaryBeing {W B : Type} [PartialOrder B] (m : Ontic W B) (w : W)
    (sum : B) (hFusion : ActualFusionAt m w sum)
    (hReflexive : ActualReflexive m w)
    (hCausal : ActualNoNecessaryPartsHaveCausesAt m w)
    (hActual : CausesHaveActualEndpointsAt m w)
    (hNonoverlap : CauseEffectNonoverlapAt m w) : NecessaryBeing m w := by
  sorry

/-- Existing owner population plus conditional selected-family formation,
local reflexivity and three causal policies. Model.explains remains unused;
no actual-part law, PSR or unconditional actual family/sum is assumed. -/
theorem fromPopulation {W B : Type} [PartialOrder B] (M : Model W B) (w : W)
    (hPopulation : PopulatedAt M w)
    (hFusion : ConditionalActualFusionAt M.ontic w)
    (hReflexive : ActualReflexive M.ontic w)
    (hCausal : ActualNoNecessaryPartsHaveCausesAt M.ontic w)
    (hActual : CausesHaveActualEndpointsAt M.ontic w)
    (hNonoverlap : CauseEffectNonoverlapAt M.ontic w) :
    NecessaryBeing M.ontic w := by
  sorry

end TruthCore.Results.Causality.ReflexiveActualFusionNecessaryBeing
