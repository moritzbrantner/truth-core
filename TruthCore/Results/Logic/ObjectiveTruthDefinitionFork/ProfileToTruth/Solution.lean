module

public import TruthCore.Logic.ObjectiveTruthDefinitionFork

@[expose] public section
namespace TruthCore.Results.Logic.ObjectiveTruthDefinitionFork.ProfileToTruth
open TruthCore.Logic
open TruthCore.Logic.ObjectiveTruthDefinitionFork

theorem profileToTruth (f : Frame) (hDefinition : ActualStableDefinition f) :
    HasTruthComponent f := by
  intro s hObjective
  exact ((hDefinition s).mp hObjective).1

end TruthCore.Results.Logic.ObjectiveTruthDefinitionFork.ProfileToTruth
