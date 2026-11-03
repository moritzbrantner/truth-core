import TruthCore.Causality.AtomisticCausalSource
import TruthCore.Causality.WorldSourceRegress
import TruthCore.Causality.ActualFusionNecessaryBeing
import TruthCore.Logic.ExcludedMiddle

namespace TruthCore.Results.Causality.AtomisticNecessaryConstituent
open TruthCore.Causality.AtomisticCausalSource
open TruthCore.Causality.WorldSourceRegress
open TruthCore.Causality.ActualFusionNecessaryBeing
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Logic (ExcludedMiddle)

/-- Eight explicit inputs yield SOME actual necessary individual, possibly a
part of the selected actual source. The source itself is not asserted necessary.
The actual subtype inherits the supplied ambient parthood order. No activity,
modal reflexivity, global well-foundedness or no-necessary-parts cover is used. -/
theorem necessaryBeing {W B : Type} [PartialOrder B] (m : Ontic W B) (w : W)
    (hPop : ObjectPopulation (Actual m w))
    (hAtomic : AtomicParts (Actual m w))
    (hCover : ConditionalCausedSimpleCover (actualGraph m w))
    (hNoOverlap : CauseEffectNonoverlap (actualGraph m w))
    (hEM : ExcludedMiddle)
    (hCausal : ActualNoNecessaryPartsHaveCausesAt m w)
    (hActual : CausesHaveActualEndpointsAt m w)
    (hParts : ActualPartsExistAt m w) : NecessaryBeing m w := by
  sorry

end TruthCore.Results.Causality.AtomisticNecessaryConstituent
