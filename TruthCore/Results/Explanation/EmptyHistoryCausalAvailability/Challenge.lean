import TruthCore.Explanation.EmptyHistoryCausalAvailability

namespace TruthCore.Results.Explanation.EmptyHistoryCausalAvailability
open TruthCore.Explanation.EmptyHistoryCausalAvailability
open TruthCore.Explanation.PSRStrength (Arena Contingent)
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt NecessaryBeing ContingentAt)
open TruthCore.Causality.NecessarilyUnderived (ActualReflexive)
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Modal (Euclidean)

theorem necessaryBeing {W B F : Type} (A : Arena W B F)
    (Concrete : B → Prop) (CauseFact : W → B → F → Prop) (w : W) (f : F)
    (hEM : ExcludedMiddle) (hEuclidean : Euclidean A.ontic.frame)
    (hReflexive : ActualReflexive A.ontic w)
    (hMeaning : NegativeFactMeaning A Concrete f)
    (hCoverage : AccessibleEmptyCoverage A Concrete CauseFact w)
    (hPositive : PossiblyInhabitedConcreteAt A Concrete w) : NecessaryBeing A.ontic w := by
  sorry

end TruthCore.Results.Explanation.EmptyHistoryCausalAvailability
