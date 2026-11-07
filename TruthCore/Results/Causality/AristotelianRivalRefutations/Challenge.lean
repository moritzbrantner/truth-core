import TruthCore.Causality.AristotelianRivalRefutations

namespace TruthCore.Results.Causality.AristotelianRivalRefutations
open TruthCore.Causality.AristotelianRivalRefutations
open TruthCore.Greek.Aristotle.Metaphysics (PotencyIsUnactualizedCapacityReading)
open TruthCore.Greek.Aristotle.Physics (BeingMovedIsActualizationOfPotencyReading)

/-- What is in potency in a respect is not in act in it. -/
theorem noActAndPotencyInSameRespect {B R : Type} (InAct InPotency CanBe : B → R → Prop)
    (hAnalysis : PotencyIsUnactualizedCapacityReading InAct InPotency CanBe) :
    NoActAndPotencyInSameRespect InAct InPotency := by
  sorry

/-- What is being moved in a respect is in potency in it. -/
theorem noMovedWithoutPotency {B R : Type} (MovedIn InPotency Actualized : B → R → Prop)
    (hAnalysis : BeingMovedIsActualizationOfPotencyReading MovedIn InPotency Actualized) :
    NoMovedWithoutPotency MovedIn InPotency := by
  sorry

theorem controls : TruthCore.Causality.AristotelianRivalRefutations.Control.Certificate := by
  sorry

end TruthCore.Results.Causality.AristotelianRivalRefutations
