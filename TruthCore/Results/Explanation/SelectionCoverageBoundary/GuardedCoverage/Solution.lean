module

public import TruthCore.Results.Explanation.SelectionCoverageBoundary.Coverage.Solution

@[expose] public section
namespace TruthCore.Results.Explanation.SelectionCoverageBoundary.GuardedCoverage
open TruthCore.Explanation.SelectionCoverageBoundary
open TruthCore.Explanation.OrderingCardinality

/-- Analyst factivity/coverage obligation; explanatory warrant remains independent. -/
theorem guardedCoverage (a : Arrangement) (adequate : (Arrangement → Prop) → Prop)
    (hEM : TruthCore.Logic.ExcludedMiddle) (hFact : AcceptedAreTrue a adequate) :
    FactiveSelectionFork a adequate := by
  cases TruthCore.Results.Explanation.SelectionCoverageBoundary.Coverage.coverage a adequate hEM with
  | inl h => exact Or.inl h
  | inr h =>
    rcases h with h | ⟨p, hp, hn⟩
    · exact Or.inr h
    · exact False.elim (hn (hFact p hp))

end TruthCore.Results.Explanation.SelectionCoverageBoundary.GuardedCoverage
