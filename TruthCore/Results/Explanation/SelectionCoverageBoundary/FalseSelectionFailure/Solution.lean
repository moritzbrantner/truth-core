module

public import TruthCore.Explanation.SelectionCoverageBoundary

@[expose] public section
namespace TruthCore.Results.Explanation.SelectionCoverageBoundary.FalseSelectionFailure
open TruthCore.Explanation.SelectionCoverageBoundary
open TruthCore.Explanation.OrderingCardinality

/-- Analyst factivity/coverage obligation; explanatory warrant remains independent. -/
theorem falseSelectionFailure (a : Arrangement) (adequate : (Arrangement → Prop) → Prop)
    (h : AcceptedFalse a adequate) : SelectionFails a adequate := by
  obtain ⟨p, hp, hn⟩ := h
  exact fun hSelect => hn (hSelect p hp).1

end TruthCore.Results.Explanation.SelectionCoverageBoundary.FalseSelectionFailure
