module

public import TruthCore.Results.Logic.MeaningDefinitionFork.V2Rejection.Solution

@[expose] public section
namespace TruthCore.Results.Logic.MeaningDefinitionFork.V2RejectionBound
open TruthCore.Logic.Verificationism
open TruthCore.Logic.MeaningDefinitionFork

/-- Same logical type as the preserved raw-form draft; named heads provide the exact corpus binding. -/
theorem v2Rejection {L : Language} (F : Frame L) (meaningful scope : L.Sentence → Prop)
    (hTarget : V2ExcludedTarget F meaningful scope) : NotV2Definition F meaningful scope := by
  exact TruthCore.Results.Logic.MeaningDefinitionFork.V2Rejection.v2Rejection F meaningful scope hTarget

end TruthCore.Results.Logic.MeaningDefinitionFork.V2RejectionBound
