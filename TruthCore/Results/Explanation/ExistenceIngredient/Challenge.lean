import TruthCore.Explanation.ExistenceIngredient

namespace TruthCore.Results.Explanation.ExistenceIngredient
open TruthCore.Explanation.ExistenceIngredient
open TruthCore.Causality.JointGroups

/-- Direct joint-record extraction. Neither WF nor member-alone sufficiency
is added to the ultimate autonomous-ground and ingredient premises. -/
theorem extract {B O G : Type} (h : Groups (Fact B O) G)
    (autonomous : Fact B O → Prop) (b : B)
    (hGround : AutonomousFullGround h autonomous b)
    (hIngredient : IngredientAt h b) :
    AutonomousExistenceIngredient h autonomous b := by
  sorry

/-- The direct extraction permits a genuinely mixed antecedent record. -/
theorem mixedCertificate : MixedCertificate := by
  sorry

end TruthCore.Results.Explanation.ExistenceIngredient
