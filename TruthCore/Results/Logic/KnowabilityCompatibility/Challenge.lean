import TruthCore.Logic.KnowabilityCompatibility

namespace TruthCore.Results.Logic.KnowabilityCompatibility
open TruthCore.Modal TruthCore.Logic.FitchKnowability
open TruthCore.Logic.KnowabilityCompatibility

/-- Euclidean sibling reach and reverse knowability force admitted knowledge.
No epistemic factivity, modal reflexivity or Moore closure is a premise. -/
theorem admittedKnown {W : Type} (E R : Frame W) (actual : W)
    (C : (W → Prop) → Prop) (euclidean : Euclidean R)
    (included : Included E R)
    (equivalence : GlobalRestrictedEquivalence (relationalContext E R actual) C) :
    AdmittedKnown (relationalContext E R actual) C := by
  sorry

theorem forwardSurvivor : ForwardSurvivor := by
  sorry

theorem lineSurvivor : LineSurvivor := by
  sorry

end TruthCore.Results.Logic.KnowabilityCompatibility
