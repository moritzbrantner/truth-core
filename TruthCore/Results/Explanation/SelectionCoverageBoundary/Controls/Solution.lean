module

public import TruthCore.Explanation.SelectionCoverageBoundary

@[expose] public section
namespace TruthCore.Results.Explanation.SelectionCoverageBoundary.Controls
open TruthCore.Explanation.SelectionCoverageBoundary
open TruthCore.Explanation.OrderingCardinality

/-- Analyst factivity/coverage obligation; explanatory warrant remains independent. -/
theorem controls : TruthCore.Explanation.SelectionCoverageBoundary.Controls := by
  intro a
  have hFalse : AcceptedFalse a (falseOnly a) := ⟨fun _ => False, fun h => h, fun h => h⟩
  have hNoFalseRival : ¬ AcceptsUnselected a (falseOnly a) :=
    TruthCore.Results.Explanation.OrderingCardinality.TruthfulRival.checks.1 a (falseOnly a) (fun _ h => h)
  have hTrueRival : AcceptsUnselected a (trueOnly a) :=
    TruthCore.Results.Explanation.OrderingCardinality.TruthfulRival.checks.2.1 a (trueOnly a) True.intro
  refine ⟨⟨hFalse, ?_, hNoFalseRival⟩, ⟨fun _ h => h, hTrueRival, ?_⟩, ?_⟩
  · intro h
    exact (h (fun _ => False) (fun h => h)).1
  · exact TruthCore.Results.Explanation.OrderingCardinality.TruthfulRival.checks.2.2 a (trueOnly a) hTrueRival
  · refine ⟨fun _ h => h, fun _ h => h.1, ?_⟩
    exact ⟨fun b => b = a, rfl, fun _ h => h⟩

end TruthCore.Results.Explanation.SelectionCoverageBoundary.Controls
