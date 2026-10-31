import TruthCore.Explanation.JointCondition

namespace TruthCore.Results.Explanation.JointCondition
open TruthCore.Explanation.PSRStrength
open TruthCore.Explanation.JointCondition

theorem contingent {W B F : Type} (A : Arena W B F) (S : Set F) (w : W)
    (hActual : JointTrue A S w) (hMember : ContingentMember A S w) :
    JointContingent A S w := by
  sorry

theorem necessityEquivalence : NecessityEquivalence := by
  sorry

theorem mixedCertificate : MixedCertificate := by
  sorry

end TruthCore.Results.Explanation.JointCondition
