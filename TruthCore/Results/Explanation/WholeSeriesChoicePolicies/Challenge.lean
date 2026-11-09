import TruthCore.Explanation.WholeSeriesChoicePolicies

namespace TruthCore.Results.Explanation.WholeSeriesChoicePolicies
open TruthCore.Explanation.WholeSeriesReason TruthCore.Explanation.WholeSeriesChoicePolicies

/-- Exact formal scopes and the full-fact tied-order control; no historical or
metaphysical adequacy premise is established. -/
theorem certificates : Certificates := by
  sorry
end TruthCore.Results.Explanation.WholeSeriesChoicePolicies

namespace TruthCore.Results.Explanation.WholeSeriesChoicePolicies
open TruthCore.Explanation.PSRStrength TruthCore.Explanation.WholeSeriesReason
open TruthCore.Explanation.WholeSeriesChoicePolicies
/-- Forget only the procedural agenda condition; all original exercise data,
including the same actual necessary bearer and complete fact valuation, survive. -/
theorem forgetSelection {W B F O : Type} (A : Arena W B F)
    (carries : W → B → F → Prop) (S : Selection W B F O) (agenda : List O) (a : W)
    (h : HasSelectedWholeExercise A carries S agenda a) :
    HasReasonGuidedWholeExercise A carries S a := by
  sorry
end TruthCore.Results.Explanation.WholeSeriesChoicePolicies
