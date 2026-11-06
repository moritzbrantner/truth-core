module

public import TruthCore.Alternatives.NaturalReasonHorizon

@[expose] public section

namespace TruthCore.Results.Alternatives.NaturalReasonHorizon.Coverage

open TruthCore.Alternatives.Fideism
open TruthCore.Alternatives.NaturalReasonHorizon

/-- Exact profile consequence; no descriptive horizon is silently negated. -/
theorem profileCoverage (P : Practice) (hEM : TruthCore.Logic.ExcludedMiddle) : NaturalReasonProfileCases P := by
  cases hEM (NaturalReasonIsSharedReading P) with
  | inl h => exact Or.inl h
  | inr hNotShared =>
    cases hEM (NaturalReasonNeverShared P) with
    | inl h => exact Or.inr (Or.inl h)
    | inr hNotNever =>
      apply Or.inr; apply Or.inr
      constructor
      · cases hEM (∃ m, P.AffirmsNaturalKnowability m ∧ P.AnswersToSharedReason m) with
        | inl h => exact h
        | inr hNone =>
          exact False.elim (hNotNever (fun m hNatural hShared => hNone ⟨m, hNatural, hShared⟩))
      · cases hEM (∃ m, P.AffirmsNaturalKnowability m ∧ ¬ P.AnswersToSharedReason m) with
        | inl h => exact h
        | inr hNone =>
          apply False.elim; apply hNotShared
          intro m hNatural
          cases hEM (P.AnswersToSharedReason m) with
          | inl h => exact h
          | inr h => exact False.elim (hNone ⟨m, hNatural, h⟩)

end TruthCore.Results.Alternatives.NaturalReasonHorizon.Coverage
