import TruthCore.Logic.MeaningDefinitionFork
import TruthCore.Results.Logic.Verificationism.Ayer1936Trivial.Solution
namespace TruthCore.Results.Logic.MeaningDefinitionFork.V2Rejection
open TruthCore.Logic.Verificationism
open TruthCore.Logic.MeaningDefinitionFork
theorem v2Rejection {L : Language} (F : Frame L) (meaningful scope : L.Sentence → Prop)
    (hTarget : V2ExcludedTarget F meaningful scope) : ¬ V2Definition F meaningful scope := by
  sorry

end TruthCore.Results.Logic.MeaningDefinitionFork.V2Rejection
