import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question14.ReceptionDefinitionFork

namespace TruthCore.Results.Aquinas.SummaTheologiae.Q14ReceptionFork
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.SummaTheologiae.FormReception
open TruthCore.Latin.Aquinas.SummaTheologiae.Q14ReceptionFork

theorem oldTargetOfCapacity {B F : Type} (m : Model B F) (scope matterForm : B → Prop)
    (component : B → B → Prop)
    (hScope : StructuralScopeCovered scope matterForm component)
    (hAvailable : StructuralCapacityAvailable m matterForm component)
    (hCalibration : CapacityCalibration m scope) :
    ImmaterialIsIntellectualReading matterForm m.Intellectual component := by
  sorry

end TruthCore.Results.Aquinas.SummaTheologiae.Q14ReceptionFork
