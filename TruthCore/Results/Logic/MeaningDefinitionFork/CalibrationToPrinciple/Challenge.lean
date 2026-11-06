import TruthCore.Logic.MeaningDefinitionFork
namespace TruthCore.Results.Logic.MeaningDefinitionFork.CalibrationToPrinciple
open TruthCore.Logic.Verificationism
open TruthCore.Logic.MeaningDefinitionFork
theorem calibrationToPrinciple {L : Language} (F : Frame L) (meaningful scope verifiable : L.Sentence → Prop)
    (h : Calibration F meaningful scope verifiable) :
    VerificationPrinciple F meaningful scope verifiable := by
  sorry

end TruthCore.Results.Logic.MeaningDefinitionFork.CalibrationToPrinciple
