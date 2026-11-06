module

public import TruthCore.Explanation.SelectionCoverageBoundary

@[expose] public section
namespace TruthCore.Results.Explanation.SelectionCoverageBoundary.FalseFactivityFailure
open TruthCore.Explanation.SelectionCoverageBoundary
open TruthCore.Explanation.OrderingCardinality

/-- Analyst factivity/coverage obligation; explanatory warrant remains independent. -/
theorem falseFactivityFailure (a : Arrangement) (adequate : (Arrangement → Prop) → Prop)
    (h : AcceptedFalse a adequate) : FactivityFails a adequate := by
  obtain ⟨p, hp, hn⟩ := h
  exact fun hFact => hn (hFact p hp)

end TruthCore.Results.Explanation.SelectionCoverageBoundary.FalseFactivityFailure
