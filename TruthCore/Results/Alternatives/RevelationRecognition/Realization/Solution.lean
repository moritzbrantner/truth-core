module

public import TruthCore.Alternatives.RevelationRecognition

@[expose] public section

namespace TruthCore.Results.Alternatives.RevelationRecognition.Realization

open TruthCore.Alternatives.Fideism
open TruthCore.Alternatives.RevelationRecognition
open TruthCore.Case.Catholicism

/-- Exact coverage obligation with outside-admitted alternative retained. -/
theorem realizationFromCandidateCoverage (σ : Signature) (R : RecognitionProfile σ)
    (hCandidate : CandidateRecognitionRealized σ R)
    (hCoverage : AdmissibleRecognitionCoverage σ R) : RecognizableCapacityRealized σ R := by
  intro g hGod hCapacity
  exact hCoverage g hGod hCapacity (hCandidate g hGod hCapacity)

end TruthCore.Results.Alternatives.RevelationRecognition.Realization
