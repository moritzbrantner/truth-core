import TruthCore.Explanation.JointContingencyLocalization

namespace TruthCore.Results.Explanation.JointContingencyLocalization
open TruthCore.Explanation.PSRStrength
open TruthCore.Explanation.JointCondition
open TruthCore.Explanation.JointContingencyLocalization

/-- A fixed contingent package has an actual contingent member. Classical
extraction retains the package's same accessible failure world. -/
theorem localize {W B F : Type} (A : Arena W B F) (S : Set F) (w : W)
    (hJoint : JointContingent A S w) : ContingentMember A S w := by
  sorry

/-- Compose localization with the existing forward contingent theorem. No
joint truth or contingency is asserted without an input to the equivalence. -/
theorem equivalence {W B F : Type} (A : Arena W B F) (S : Set F) (w : W) :
    Equivalence A S w := by
  sorry

end TruthCore.Results.Explanation.JointContingencyLocalization
