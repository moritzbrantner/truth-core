module

public import TruthCore.Case.Catholicism.StageThree.ChurchDefinitions

@[expose] public section

namespace TruthCore.Results.Case.Catholicism.StageThree.ChurchDefinitions.Coverage

open TruthCore.Case.Catholicism
open TruthCore.Case.Catholicism.StageThree.ChurchDefinitions

/-- Exact selected-criterion consequence; no source reading or history is established. -/
theorem criterionCoverage (σ : Signature) (church spiritual : σ.Society → Prop)
    (hEM : TruthCore.Logic.ExcludedMiddle) : ChurchCriterionCases σ church spiritual := by
  cases hEM (VisibleCriterion σ church) with
  | inl h => exact Or.inl h
  | inr hV =>
    cases hEM (SpiritualCriterion σ church spiritual) with
    | inl h => exact Or.inr (Or.inl h)
    | inr hS =>
      cases hEM (JointAspectCriterion σ church spiritual) with
      | inl h => exact Or.inr (Or.inr (Or.inl h))
      | inr hJ => exact Or.inr (Or.inr (Or.inr ⟨hV, hS, hJ⟩))

end TruthCore.Results.Case.Catholicism.StageThree.ChurchDefinitions.Coverage
