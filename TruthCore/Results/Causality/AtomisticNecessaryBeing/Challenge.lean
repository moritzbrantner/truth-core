import TruthCore.Causality.AtomisticCausalSource
import TruthCore.Logic.ExcludedMiddle
import TruthCore.Causality.WorldSourceRegress

namespace TruthCore.Results.Causality.AtomisticNecessaryBeing
open TruthCore.Causality.AtomisticCausalSource
open TruthCore.Causality.WorldSourceRegress
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Logic (ExcludedMiddle)

/-- Conditional complete-production interpretation on actual objects only.
No concreteness, grounding identity, activity or modal frame law is assumed. -/
theorem necessaryBeing {W B : Type} (m : Ontic W B) (w : W)
    [PartialOrder (Actual m w)]
    (hPop : ObjectPopulation (Actual m w))
    (hAtomic : AtomicParts (Actual m w))
    (hCover : ConditionalCausedSimpleCover (actualGraph m w))
    (hNoOverlap : CauseEffectNonoverlap (actualGraph m w))
    (hEM : ExcludedMiddle) (hCausal : LocalCausalPrinciple m) :
    NecessaryBeing m w := by
  sorry

end TruthCore.Results.Causality.AtomisticNecessaryBeing
