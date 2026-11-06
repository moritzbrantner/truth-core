module

public import TruthCore.Explanation.SelectionCoverageBoundary

@[expose] public section
namespace TruthCore.Results.Explanation.SelectionCoverageBoundary.Coverage
open TruthCore.Explanation.SelectionCoverageBoundary
open TruthCore.Explanation.OrderingCardinality

/-- Analyst factivity/coverage obligation; explanatory warrant remains independent. -/
theorem coverage (a : Arrangement) (adequate : (Arrangement → Prop) → Prop)
    (hEM : TruthCore.Logic.ExcludedMiddle) : SelectionTrilemma a adequate := by
  cases hEM (AcceptsUnselected a adequate) with
  | inl h => exact Or.inr (Or.inl h)
  | inr hNoRival =>
    cases hEM (AcceptedFalse a adequate) with
    | inl h => exact Or.inr (Or.inr h)
    | inr hNoFalse =>
      left
      intro p hp
      have hTruth : p a := by
        cases hEM (p a) with
        | inl h => exact h
        | inr h => exact False.elim (hNoFalse ⟨p, hp, h⟩)
      refine ⟨hTruth, ?_⟩
      intro b hb
      cases hEM (b = a) with
      | inl h => exact h
      | inr h => exact False.elim (hNoRival ⟨p, hp, hTruth, b, h, hb⟩)

end TruthCore.Results.Explanation.SelectionCoverageBoundary.Coverage
