import TruthCore.Causality.ContingentAtomicity
import TruthCore.Logic.ExcludedMiddle

namespace TruthCore.Results.Causality.ContingentAtomicity
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Causality.WorldSourceRegress
open TruthCore.Causality.AtomisticCausalSource
open TruthCore.Causality.ScopedActualCausality
open TruthCore.Causality.ContingentAtomicity
open TruthCore.Logic (ExcludedMiddle)

theorem allToContingent {W B : Type} (m : Ontic W B) (w : W)
    [PartialOrder (Actual m w)] (hAtomic : AtomicParts (Actual m w)) :
    ContingentAtomicParts m w := by
  sorry

theorem necessaryBeing {W B : Type} (m : Ontic W B) (w : W)
    [PartialOrder (Actual m w)]
    (hPop : ObjectPopulation (Actual m w)) (hAtomic : ContingentAtomicParts m w)
    (hCover : ConditionalCausedSimpleCover (actualGraph m w))
    (hNoOverlap : CauseEffectNonoverlap (actualGraph m w))
    (hEM : ExcludedMiddle) (hCoverage : SelectedActualCausalCoverage m w) :
    NecessaryBeing m w := by
  sorry

theorem control : Control := by
  sorry

end TruthCore.Results.Causality.ContingentAtomicity
