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
  rcases hGround with ⟨g, hg, he, hAll⟩
  obtain ⟨f, hf, hExist⟩ := hIngredient g hg he
  exact ⟨g, hg, he, hAll, f, hf, hExist, hAll f hf⟩

/-- The direct extraction permits a genuinely mixed antecedent record. -/
theorem mixedCertificate : MixedCertificate := by
  have hGround : AutonomousFullGround mixed mixedAutonomous () := by
    refine ⟨(), trivial, rfl, ?_⟩
    intro f hf
    change f = essential () ∨ f = other () at hf
    exact hf
  have hIngredient : IngredientAt mixed () := by
    intro g _ _
    refine ⟨essential (), Or.inl rfl, trivial⟩
  refine ⟨hGround, hIngredient, extract mixed mixedAutonomous () hGround hIngredient, ?_⟩
  exact ⟨other (), Or.inr rfl, id⟩

end TruthCore.Results.Explanation.ExistenceIngredient
