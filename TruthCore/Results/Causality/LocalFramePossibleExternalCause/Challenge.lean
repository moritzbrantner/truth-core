import TruthCore.Causality.LocalFramePossibleExternalCause

namespace TruthCore.Results.Causality.LocalFramePossibleExternalCause
open TruthCore.Causality.LocalFramePossibleExternalCause
open TruthCore.Causality.PossibleCauseOfContingency
open TruthCore.Causality.NecessarilyUnderived (ActualReflexive)
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt)
open TruthCore.Modal (Euclidean)

theorem necessaryConcrete {W B : Type} (s : Scenario W B) (w : W)
    (hEuclidean : Euclidean s.ontic.frame)
    (hReflexive : ActualReflexive s.ontic w)
    (hBeginning : PossiblyBeginsAt s w)
    (hOpportunity : CausalOpportunityAt s w) : NecessaryConcreteAt s w := by
  sorry

end TruthCore.Results.Causality.LocalFramePossibleExternalCause
