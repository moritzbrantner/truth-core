import TruthCore.Results.Logic.MeaningDefinitionFork.V2Rejection.Solution
namespace TruthCore.Results.Logic.MeaningDefinitionFork.V2RejectionBound
open TruthCore.Logic.Verificationism
open TruthCore.Logic.MeaningDefinitionFork
theorem v2Rejection {L : Language} (F : Frame L) (meaningful scope : L.Sentence → Prop)
    (hTarget : V2ExcludedTarget F meaningful scope) : NotV2Definition F meaningful scope := by
  sorry
end TruthCore.Results.Logic.MeaningDefinitionFork.V2RejectionBound
