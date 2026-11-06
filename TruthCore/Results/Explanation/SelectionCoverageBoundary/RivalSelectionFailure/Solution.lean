module

public import TruthCore.Explanation.SelectionCoverageBoundary

@[expose] public section
namespace TruthCore.Results.Explanation.SelectionCoverageBoundary.RivalSelectionFailure
open TruthCore.Explanation.SelectionCoverageBoundary
open TruthCore.Explanation.OrderingCardinality

/-- Analyst factivity/coverage obligation; explanatory warrant remains independent. -/
theorem rivalSelectionFailure (a : Arrangement) (adequate : (Arrangement → Prop) → Prop)
    (h : AcceptsUnselected a adequate) : SelectionFails a adequate := by
  exact TruthCore.Results.Explanation.OrderingCardinality.TruthfulRival.checks.2.2 a adequate h

end TruthCore.Results.Explanation.SelectionCoverageBoundary.RivalSelectionFailure
