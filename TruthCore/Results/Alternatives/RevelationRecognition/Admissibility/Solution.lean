module

public import TruthCore.Alternatives.RevelationRecognition

@[expose] public section

namespace TruthCore.Results.Alternatives.RevelationRecognition.Admissibility

open TruthCore.Alternatives.Fideism
open TruthCore.Alternatives.RevelationRecognition
open TruthCore.Case.Catholicism

/-- Exact coverage obligation with outside-admitted alternative retained. -/
theorem admissibilityCoverage (σ : Signature) (R : RecognitionProfile σ)
    (hEM : TruthCore.Logic.ExcludedMiddle) : RecognitionAdmissibilityCases σ R := by
  cases hEM (AdmissibleRecognitionCoverage σ R) with
  | inl h => exact Or.inl h
  | inr hNoCoverage =>
    cases hEM (OutsideAdmissibleRecognition σ R) with
    | inl h => exact Or.inr h
    | inr hNoOutside =>
      apply False.elim
      apply hNoCoverage
      intro g hGod hCapacity hCandidate
      cases hEM (PossibleCorrectRecognition σ R g) with
      | inl h => exact h
      | inr hNoPossible =>
        obtain ⟨s, m, hRecognizes, hCorrect⟩ := hCandidate
        have hNotAdmissible : ¬ R.admissible s := by
          intro hAdmissible
          exact hNoPossible ⟨s, hAdmissible, m, hRecognizes, hCorrect⟩
        exact False.elim (hNoOutside
          ⟨g, hGod, hCapacity, s, hNotAdmissible, m, hRecognizes, hCorrect, hNoPossible⟩)

end TruthCore.Results.Alternatives.RevelationRecognition.Admissibility
