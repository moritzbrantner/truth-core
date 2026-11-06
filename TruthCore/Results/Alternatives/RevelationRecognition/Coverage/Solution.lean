module

public import TruthCore.Alternatives.RevelationRecognition

@[expose] public section

namespace TruthCore.Results.Alternatives.RevelationRecognition.Coverage

open TruthCore.Alternatives.Fideism
open TruthCore.Alternatives.RevelationRecognition
open TruthCore.Case.Catholicism

/-- Exact scope comparison; no actual recognition is inferred from capability. -/
theorem bridgeCoverage (σ : Signature) (R : RecognitionProfile σ)
    (hEM : TruthCore.Logic.ExcludedMiddle) : RecognitionBridgeCasesCover σ R := by
  cases hEM (RecognizableCapacityRealized σ R) with
  | inr h => exact Or.inr (Or.inl h)
  | inl hRealized =>
    cases hEM (RecognitionAnswersToSharedReason σ R) with
    | inl hShared => exact Or.inl ⟨hRealized, hShared⟩
    | inr h => exact Or.inr (Or.inr h)

end TruthCore.Results.Alternatives.RevelationRecognition.Coverage
