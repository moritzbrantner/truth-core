import TruthCore.Causality.LifeBoundaryPotency

namespace TruthCore.Results.Causality.LifeBoundaryPotency
open TruthCore.Causality.LifeBoundaryPotency
open TruthCore.Latin.Aquinas.SummaTheologiae (LifeBoundaryRequiresPotencyReading)
open TruthCore.Logic (ExcludedMiddle)

/-- Contrapositive of q.10 a.1 under excluded middle. Conditional on two OPEN
premises. -/
theorem lifeBoundaryRequiresPotency {B R T : Type} [LT T] (InPotency : B → R → Prop)
    (LivesAt : B → T → Prop) (hEM : ExcludedMiddle)
    (hImmutable : ImmutableHasNoLifeBoundary InPotency LivesAt) :
    LifeBoundaryRequiresPotencyReading InPotency LivesAt := by
  sorry

theorem controls : TruthCore.Causality.LifeBoundaryPotency.Control.Certificate := by
  sorry

end TruthCore.Results.Causality.LifeBoundaryPotency
