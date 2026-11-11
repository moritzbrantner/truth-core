import TruthCore.Explanation.AutonomousGroundConcrete
import TruthCore.Results.Explanation.AutonomousGroundNecessity.Solution

namespace TruthCore.Results.Explanation.AutonomousGroundConcrete
open TruthCore.Explanation.AutonomousGroundConcrete
open TruthCore.Explanation.AutonomousGroundNecessity
open TruthCore.Explanation.ExistenceIngredient
open TruthCore.Explanation.PSRStrength (Arena)
open TruthCore.Causality.JointGroups
open TruthCore.Causality.BruteFoundationBoundary

/-- Assembly only: reuse sameTarget on the supplied Profile's exact ontology
and concrete predicate; the witness is the original target, never a replacement. -/
theorem necessaryConcrete {W B O G : Type} (m : Profile W B)
    (holds : W → Fact B O → Prop) (explains : W → Fact B O → Fact B O → Prop)
    (conjunct : Fact B O → Fact B O → Prop) (exist : B → Fact B O)
    (h : Groups (Fact B O) G) (autonomous : Fact B O → Prop) (w : W) (b : B)
    (hActual : ActualConcreteTargetAt ⟨m.ontic, holds, exist, explains, conjunct⟩ m.concrete w b)
    (hGround : AutonomousFullGround h autonomous b)
    (hAutonomous : AutonomousFactsNecessaryAt ⟨m.ontic, holds, exist, explains, conjunct⟩ autonomous w)
    (hNecessitates : WholeGroundNecessitatesTargetAt ⟨m.ontic, holds, exist, explains, conjunct⟩ h w b)
    (hCoherent : PositiveTargetCoherent ⟨m.ontic, holds, exist, explains, conjunct⟩ b) :
    NecessaryConcreteAt m w := by
  sorry

/-- Populated same-model compatibility certificate, not metaphysical possibility. -/
theorem certificate : TruthCore.Explanation.AutonomousGroundConcrete.Certificate := by
  sorry

end TruthCore.Results.Explanation.AutonomousGroundConcrete
