import TruthCore.Explanation.AutonomousGroundNecessity
import TruthCore.Results.Explanation.JointCondition.Solution
import TruthCore.Causality.BruteFoundationRoutes

namespace TruthCore.Results.Explanation.AutonomousGroundNecessity
open TruthCore.Explanation.AutonomousGroundNecessity
open TruthCore.Explanation.ExistenceIngredient
open TruthCore.Explanation.PSRStrength (Arena Access)
open TruthCore.Explanation.JointCondition
open TruthCore.Causality.JointGroups (Groups)
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt NecessaryBeing)

/-- Import memberwise/joint necessity on the exact full record, then apply
WHOLE-ground necessitation and the aligned positive existence fact's meaning.
No existential ingredient or necessity of a single chosen member is substituted. -/
theorem necessaryTarget {W B O G : Type} (A : Arena W B (Fact B O))
    (h : Groups (Fact B O) G) (autonomous : Fact B O → Prop) (w : W) (b : B)
    (hGround : AutonomousFullGround h autonomous b)
    (hAutonomous : AutonomousFactsNecessaryAt A autonomous w)
    (hNecessitates : WholeGroundNecessitatesTargetAt A h w b)
    (hCoherent : PositiveTargetCoherent A b) : NecessaryAt A.ontic w b := by
  obtain ⟨g, hg, he, hAll⟩ := hGround
  have hMembers : MembersNecessary A (h.members g) w := by
    intro f hf v hv
    exact hAutonomous f (hAll f hf) v hv
  have hJoint : JointNecessary A (h.members g) w :=
    (TruthCore.Results.Explanation.JointCondition.necessityEquivalence
      W B (Fact B O) A (h.members g) w).mpr hMembers
  intro v hv
  have hFact := hNecessitates g hg he v hv (hJoint v hv)
  apply (hCoherent.2 v).mp
  rw [hCoherent.1]
  exact hFact

/-- Preserve the PARTICULAR actual concrete target; no new witness replaces it. -/
theorem sameTarget {W B O G : Type} (A : Arena W B (Fact B O))
    (h : Groups (Fact B O) G) (autonomous : Fact B O → Prop)
    (Concrete : B → Prop) (w : W) (b : B)
    (hActual : ActualConcreteTargetAt A Concrete w b)
    (hGround : AutonomousFullGround h autonomous b)
    (hAutonomous : AutonomousFactsNecessaryAt A autonomous w)
    (hNecessitates : WholeGroundNecessitatesTargetAt A h w b)
    (hCoherent : PositiveTargetCoherent A b) :
    Concrete b ∧ A.ontic.ExistsAt w b ∧ NecessaryAt A.ontic w b := by
  exact ⟨hActual.1, hActual.2,
    necessaryTarget A h autonomous w b hGround hAutonomous hNecessitates hCoherent⟩

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
  obtain ⟨_, he, hn⟩ :=
    sameTarget A h autonomous Concrete w b hActual hGround hAutonomous hNecessitates hCoherent
  exact ⟨b, he, hn⟩

/-- The same four explanatory/modal inputs already exclude contingency of
this particular target; actual target admission is unnecessary here. -/
theorem targetNotContingent {W B O G : Type} (A : Arena W B (Fact B O))
    (h : Groups (Fact B O) G) (autonomous : Fact B O → Prop) (w : W) (b : B)
    (hGround : AutonomousFullGround h autonomous b)
    (hAutonomous : AutonomousFactsNecessaryAt A autonomous w)
    (hNecessitates : WholeGroundNecessitatesTargetAt A h w b)
    (hCoherent : PositiveTargetCoherent A b) : TargetNotContingentAt A w b := by
  intro hContingent
  have hn := necessaryTarget A h autonomous w b hGround hAutonomous hNecessitates hCoherent
  exact TruthCore.Causality.BruteFoundationRoutes.noContingentEffectFromNecessaryStrictSufficiency
    A.ontic w b b hn (fun _ _ hx => hx) hContingent.2

end TruthCore.Results.Explanation.AutonomousGroundNecessity
