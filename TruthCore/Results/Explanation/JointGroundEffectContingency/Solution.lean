import TruthCore.Explanation.JointGroundEffectContingency
import TruthCore.Results.Explanation.JointContingencyLocalization.Solution

namespace TruthCore.Results.Explanation.JointGroundEffectContingency
open TruthCore.Explanation.PSRStrength
open TruthCore.Explanation.ExistenceIngredient
open TruthCore.Explanation.JointCondition
open TruthCore.Explanation.AutonomousGroundNecessity
open TruthCore.Explanation.JointGroundEffectContingency
open TruthCore.Causality.JointGroups

/-- Joint necessitation plus contingency of the selected effect makes the
actually true fixed full member condition contingent at the SAME failure v. -/
theorem jointContingent {W B O G : Type} (A : Arena W B (Fact B O))
    (h : Groups (Fact B O) G) (w : W) (g : G) (b : B)
    (hJoint : JointTrue A (h.members g) w)
    (hEffect : Contingent A w (positive b))
    (hNecessitates : WholeGroundNecessitatesTargetAt A h w b)
    (hSelected : SelectedPositiveGround h g b) :
    JointContingent A (h.members g) w := by
  rcases hEffect with ⟨_hPresent, v, hAccess, hAbsent⟩
  exact ⟨hJoint, v, hAccess, fun hAll =>
    hAbsent (hNecessitates g hSelected.1 hSelected.2 v hAccess hAll)⟩

/-- Import classical localization after the constructive joint step; no
particular member's identity or cause/choice/bearer role is established. -/
theorem contingentMember {W B O G : Type} (A : Arena W B (Fact B O))
    (h : Groups (Fact B O) G) (w : W) (g : G) (b : B)
    (hJoint : JointTrue A (h.members g) w)
    (hEffect : Contingent A w (positive b))
    (hNecessitates : WholeGroundNecessitatesTargetAt A h w b)
    (hSelected : SelectedPositiveGround h g b) :
    ContingentMember A (h.members g) w := by
  exact TruthCore.Results.Explanation.JointContingencyLocalization.localize
    A (h.members g) w (jointContingent A h w g b hJoint hEffect hNecessitates hSelected)

end TruthCore.Results.Explanation.JointGroundEffectContingency
