module
public import TruthCore.Logic.MoralAttitudeProfiles
@[expose] public section
namespace TruthCore.Logic.MoralAttitudeCalibration
open MoralAttitudeProfiles
def InterventionCalibrationTruth : Prop :=
  ∀ p : Profile, (∀ s, p.truth.objective s ↔ InterventionObject p s) →
    ObjectiveTruthDefinitionFork.HasTruthComponent p.truth
def GroundingCalibrationTruth : Prop :=
  ∀ p : Profile, (∀ s, p.truth.objective s ↔ GroundingObject p s) →
    ObjectiveTruthDefinitionFork.HasTruthComponent p.truth
end TruthCore.Logic.MoralAttitudeCalibration
