import TruthCore.Causality.PossibleCausalSourceNecessity

namespace TruthCore.Results.Causality.PossibleCausalSourceNecessity
open TruthCore.Causality.PossibleCausalSourceNecessity
open TruthCore.Causality.NecessarilyUnderived (ActualReflexive)
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Modal (Euclidean)

theorem necessaryBeing {W B : Type} (m : Ontic W B) (w : W)
    (hEM : ExcludedMiddle) (hCausal : LocalCausalPrinciple m)
    (hEuclidean : Euclidean m.frame) (hReflexive : ActualReflexive m w)
    (hPossible : PossiblyFailedHeadlessCoverage m w) : NecessaryBeing m w := by
  sorry

end TruthCore.Results.Causality.PossibleCausalSourceNecessity
