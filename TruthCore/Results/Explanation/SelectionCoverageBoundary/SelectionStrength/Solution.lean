module

public import TruthCore.Explanation.SelectionCoverageBoundary

@[expose] public section
namespace TruthCore.Results.Explanation.SelectionCoverageBoundary.SelectionStrength
open TruthCore.Explanation.SelectionCoverageBoundary
open TruthCore.Explanation.OrderingCardinality

/-- Analyst factivity/coverage obligation; explanatory warrant remains independent. -/
theorem selectionStrength (a : Arrangement) (adequate : (Arrangement → Prop) → Prop)
    (h : CompleteRequiresSelection a adequate) : AcceptedAreTrue a adequate := by
  exact fun p hp => (h p hp).1

end TruthCore.Results.Explanation.SelectionCoverageBoundary.SelectionStrength
