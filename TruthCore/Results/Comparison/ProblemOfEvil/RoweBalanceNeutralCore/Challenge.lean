import TruthCore.English.Rowe.BalanceNeutralRefinement
import TruthCore.Results.Comparison.ProblemOfEvil.RoweDeductiveCore.Solution

namespace TruthCore.Results.Comparison.ProblemOfEvil.RoweBalanceNeutralCore
open TruthCore.English.Rowe

/-- The footnote refinement retains the consequence but changes both premises. -/
theorem roweBalanceNeutralCore (s : Sig)
    (BalanceNeutralGoodLoss : s.Outcome → s.Event → Prop)
    (hGratuitous : RefinedGratuitousSufferingReading s BalanceNeutralGoodLoss)
    (hPermission : RefinedPermissionConstraintReading s BalanceNeutralGoodLoss) :
    NoTheisticBeing s := by
  sorry

end TruthCore.Results.Comparison.ProblemOfEvil.RoweBalanceNeutralCore
