import TruthCore.Explanation.AutonomousGroundNecessity

namespace TruthCore.Results.Explanation.AutonomousGroundNecessity
open TruthCore.Explanation.AutonomousGroundNecessity
open TruthCore.Explanation.ExistenceIngredient
open TruthCore.Explanation.PSRStrength (Arena)
open TruthCore.Causality.JointGroups (Groups)
open TruthCore.German.Kant.CosmologicalInference (NecessaryBeing)

/-- Five explicit selected-target inputs give the existing necessary-being
endpoint. The strong source commitments are not inferred from bare PSR. -/
theorem necessaryBeing {W B O G : Type} (A : Arena W B (Fact B O))
    (h : Groups (Fact B O) G) (autonomous : Fact B O → Prop)
    (Concrete : B → Prop) (w : W) (b : B)
    (hActual : ActualConcreteTargetAt A Concrete w b)
    (hGround : AutonomousFullGround h autonomous b)
    (hAutonomous : AutonomousFactsNecessaryAt A autonomous w)
    (hNecessitates : WholeGroundNecessitatesTargetAt A h w b)
    (hCoherent : PositiveTargetCoherent A b) : NecessaryBeing A.ontic w := by
  sorry

/-- The same four explanatory/modal inputs already exclude contingency of
this particular target; actual target admission is unnecessary here. -/
theorem targetNotContingent {W B O G : Type} (A : Arena W B (Fact B O))
    (h : Groups (Fact B O) G) (autonomous : Fact B O → Prop) (w : W) (b : B)
    (hGround : AutonomousFullGround h autonomous b)
    (hAutonomous : AutonomousFactsNecessaryAt A autonomous w)
    (hNecessitates : WholeGroundNecessitatesTargetAt A h w b)
    (hCoherent : PositiveTargetCoherent A b) : TargetNotContingentAt A w b := by
  sorry

end TruthCore.Results.Explanation.AutonomousGroundNecessity
