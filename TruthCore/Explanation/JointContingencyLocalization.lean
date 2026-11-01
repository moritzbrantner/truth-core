import TruthCore.Explanation.JointCondition

/-!
Classical localization for the existing fixed conjunction. No aggregate fact,
being, cause, choice or productive role is introduced. The same selected set
and original Arena are retained; the old JointCondition definitions are not
changed. A logical equivalence neither asserts joint contingency nor selects a
particular member independently of the supplied contingent package.
-/
namespace TruthCore.Explanation.JointContingencyLocalization
open TruthCore.Explanation.PSRStrength
open TruthCore.Explanation.JointCondition

/-- Under classical logic, a fixed conjunction is contingent exactly when it
is actually true and has at least one contingent selected member. This says
neither that every member is contingent nor that a member explains an effect. -/
def Equivalence {W B F : Type} (A : Arena W B F) (S : Set F) (w : W) : Prop :=
  JointContingent A S w ↔ JointTrue A S w ∧ ContingentMember A S w

end TruthCore.Explanation.JointContingencyLocalization
