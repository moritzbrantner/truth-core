module

public import TruthCore.Alternatives.RevelationRecognition
public import TruthCore.Results.Alternatives.RevelationRecognition.Capability.Solution
public import TruthCore.Results.Alternatives.RevelationRecognition.Persistence.Solution

@[expose] public section

namespace TruthCore.Results.Alternatives.RevelationRecognition.Composition

open TruthCore.Alternatives.Fideism
open TruthCore.Alternatives.RevelationRecognition
open TruthCore.Case.Catholicism

/-- Exact scope comparison; no actual recognition is inferred from capability. -/
theorem actualInsulationRejectsCapability (σ : Signature) (R : RecognitionProfile σ)
    (hExists : GodExists σ.IsGod)
    (hRealized : RecognizableCapacityRealized σ R)
    (hShared : RecognitionAnswersToSharedReason σ R)
    (hActual : CutOffReading (R.practice R.actual))
    (hPersistence : CutOffPersistsToAdmissible σ R) : RevelationCapabilityRejected σ := by
  exact TruthCore.Results.Alternatives.RevelationRecognition.Capability.insulationRejectsCapability
    σ R hExists hRealized hShared
    (TruthCore.Results.Alternatives.RevelationRecognition.Persistence.actualCutOffPersists
      σ R hActual hPersistence)

end TruthCore.Results.Alternatives.RevelationRecognition.Composition
