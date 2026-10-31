import TruthCore.Results.Causality.ConcreteExistentialSupply.Solution

namespace TruthCore.Results.Causality.NecessaryWitnessConnection
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.ConcreteExistentialSupply
open TruthCore.German.Kant.CosmologicalInference

/-- Logical weakening in the SAME ontology: retain this witness's actual and
necessary existence while dropping its concrete predicate. This does not give
concreteness to a different witness selected by a downstream theorem. -/
theorem necessaryBearer {W B : Type} (m : Profile W B) (w : W)
    (h : NecessaryConcreteAt m w) : NecessaryBeing m.ontic w := by
  obtain ⟨individual, _, hExists, hNecessary⟩ := h
  exact ⟨individual, hExists, hNecessary⟩

/-- The complete borrowing-cut route supplies the existing general necessary-
bearer statement rather than restating necessary population as a fresh premise.
No additional philosophical assumption is introduced by the weakening. -/
theorem fromBorrowingEscape {W B : Type} (m : Profile W B) (w : W)
    (hPop : TruthCore.Logic.CogitoConcrete.InhabitedConcreteAt m.ontic m.concrete w)
    (hEscape : ActualConcreteBorrowingEscape m w)
    (hDep : EveryContingentGroundedAt m w)
    (hEM : TruthCore.Logic.ExcludedMiddle) : NecessaryBeing m.ontic w := by
  exact necessaryBearer m w
    (TruthCore.Results.Causality.ConcreteExistentialSupply.necessaryConcreteOfBorrowingEscape
      m w hPop hEscape hDep hEM)

end TruthCore.Results.Causality.NecessaryWitnessConnection
