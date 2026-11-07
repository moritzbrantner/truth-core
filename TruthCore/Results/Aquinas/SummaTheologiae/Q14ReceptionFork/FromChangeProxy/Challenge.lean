import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question14.ReceptionDefinitionFork

namespace TruthCore.Results.Aquinas.SummaTheologiae.Q14ReceptionFork
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.SummaTheologiae.FormReception
open TruthCore.Latin.Aquinas.SummaTheologiae.Q14ReceptionFork

theorem oldTargetOfChangeProxy {B F E S : Type} (m : Model B F)
    (a : ChangeProfile B F E S) (scope matterForm : B → Prop) (component : B → B → Prop)
    (hScope : StructuralScopeCovered scope matterForm component)
    (hAvailable : StructuralChangeAvailable m a matterForm component)
    (hCalibration : ChangeProxyCalibration m a scope) :
    ImmaterialIsIntellectualReading matterForm m.Intellectual component := by
  sorry

end TruthCore.Results.Aquinas.SummaTheologiae.Q14ReceptionFork
