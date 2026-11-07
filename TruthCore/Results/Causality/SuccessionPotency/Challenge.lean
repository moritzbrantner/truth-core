import TruthCore.Causality.SuccessionPotency

namespace TruthCore.Results.Causality.SuccessionPotency
open TruthCore.Causality.SuccessionPotency
open TruthCore.Latin.Aquinas.SummaTheologiae (SuccessionRequiresPotencyReading)
open TruthCore.Greek.Aristotle.Physics (BeingMovedIsActualizationOfPotencyReading)

/-- A succession of life-states is a being moved, and whatever is being moved is
in potency in that respect. Conditional on two OPEN premises. -/
theorem successionRequiresPotency {B R T S : Type} [LT T]
    (InPotency MovedIn ActualizedQuaPotential : B → R → Prop)
    (LivesAt : B → T → Prop) (lifeStateAt : B → T → S)
    (hSuccession : SuccessionIsBeingMoved LivesAt lifeStateAt MovedIn)
    (hMotion : BeingMovedIsActualizationOfPotencyReading MovedIn InPotency ActualizedQuaPotential) :
    SuccessionRequiresPotencyReading InPotency LivesAt lifeStateAt := by
  sorry

theorem controls : TruthCore.Causality.SuccessionPotency.Control.Certificate := by
  sorry

end TruthCore.Results.Causality.SuccessionPotency
