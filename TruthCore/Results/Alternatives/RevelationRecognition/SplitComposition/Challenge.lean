module

public import TruthCore.Alternatives.RevelationRecognition

public import TruthCore.Results.Alternatives.RevelationRecognition.Composition.Solution
public import TruthCore.Results.Alternatives.RevelationRecognition.Realization.Solution

@[expose] public section

namespace TruthCore.Results.Alternatives.RevelationRecognition.SplitComposition

open TruthCore.Alternatives.Fideism
open TruthCore.Alternatives.RevelationRecognition
open TruthCore.Case.Catholicism

/-- Capability rejection with candidate-carrier and admitted-subset burdens split. -/
theorem actualInsulationRejectsCapabilityWithCoverage (σ : Signature) (R : RecognitionProfile σ)
    (hExists : GodExists σ.IsGod)
    (hCandidate : CandidateRecognitionRealized σ R)
    (hCoverage : AdmissibleRecognitionCoverage σ R)
    (hShared : RecognitionAnswersToSharedReason σ R)
    (hActual : CutOffReading (R.practice R.actual))
    (hPersistence : CutOffPersistsToAdmissible σ R) : RevelationCapabilityRejected σ := by
  sorry

end TruthCore.Results.Alternatives.RevelationRecognition.SplitComposition
