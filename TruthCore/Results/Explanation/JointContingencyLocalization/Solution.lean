import TruthCore.Explanation.JointContingencyLocalization
import TruthCore.Results.Explanation.JointCondition.Solution

namespace TruthCore.Results.Explanation.JointContingencyLocalization
open TruthCore.Explanation.PSRStrength
open TruthCore.Explanation.JointCondition
open TruthCore.Explanation.JointContingencyLocalization

/-- Localize failure at this supplied v, keeping actual truth of the member.
Classical extraction does not identify the member as a choice or cause. -/
theorem memberAtFailure {W B F : Type} (A : Arena W B F) (S : Set F) (w v : W)
    (hActual : JointTrue A S w) (hFailure : ¬ JointTrue A S v) :
    ∃ f ∈ S, A.holds w f ∧ ¬ A.holds v f := by
  exact Classical.byContradiction fun hNone =>
    hFailure fun f hf =>
      Classical.byContradiction fun hAbsent =>
        hNone ⟨f, hf, hActual f hf, hAbsent⟩

/-- A fixed contingent package has an actual contingent member. Classical
extraction retains the package's same accessible failure world. -/
theorem localize {W B F : Type} (A : Arena W B F) (S : Set F) (w : W)
    (hJoint : JointContingent A S w) : ContingentMember A S w := by
  rcases hJoint with ⟨hActual, v, hAccess, hFailure⟩
  obtain ⟨f, hf, hPresent, hAbsent⟩ := memberAtFailure A S w v hActual hFailure
  exact ⟨f, hf, hPresent, v, hAccess, hAbsent⟩

/-- Compose localization with the existing forward contingent theorem. No
joint truth or contingency is asserted without an input to the equivalence. -/
theorem equivalence {W B F : Type} (A : Arena W B F) (S : Set F) (w : W) :
    Equivalence A S w := by
  constructor
  · intro hJoint
    exact ⟨hJoint.1, localize A S w hJoint⟩
  · rintro ⟨hActual, hMember⟩
    exact TruthCore.Results.Explanation.JointCondition.contingent A S w hActual hMember

end TruthCore.Results.Explanation.JointContingencyLocalization
