module
public import TruthCore.Logic.MoralAttitudeCalibration
public import TruthCore.Results.Logic.MoralAttitudeProfiles.Solution
@[expose] public section
namespace TruthCore.Results.Logic.MoralAttitudeCalibration
open TruthCore.Logic.MoralAttitudeCalibration
theorem interventionCalibration : InterventionCalibrationTruth := by
  intro p h
  exact MoralAttitudeProfiles.calibrationTruth p (Or.inl h)
theorem groundingCalibration : GroundingCalibrationTruth := by
  intro p h
  exact MoralAttitudeProfiles.calibrationTruth p (Or.inr h)
end TruthCore.Results.Logic.MoralAttitudeCalibration
