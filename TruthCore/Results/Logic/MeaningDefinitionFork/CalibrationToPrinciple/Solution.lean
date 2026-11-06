module

public import TruthCore.Logic.MeaningDefinitionFork

@[expose] public section
namespace TruthCore.Results.Logic.MeaningDefinitionFork.CalibrationToPrinciple
open TruthCore.Logic.Verificationism
open TruthCore.Logic.MeaningDefinitionFork
theorem calibrationToPrinciple {L : Language} (F : Frame L) (meaningful scope verifiable : L.Sentence → Prop)
    (h : Calibration F meaningful scope verifiable) :
    VerificationPrinciple F meaningful scope verifiable := by
  intro s hs hm
  exact (h s hs).mp hm

end TruthCore.Results.Logic.MeaningDefinitionFork.CalibrationToPrinciple
