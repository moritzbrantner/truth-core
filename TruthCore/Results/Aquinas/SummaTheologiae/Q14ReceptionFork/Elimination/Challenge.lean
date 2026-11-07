import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question14.ReceptionDefinitionFork

namespace TruthCore.Results.Aquinas.SummaTheologiae.Q14ReceptionFork
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.SummaTheologiae.FormReception
open TruthCore.Latin.Aquinas.SummaTheologiae.Q14ReceptionFork

theorem changeProxyOfElimination {B F E S : Type} (m : Model B F)
    (a : ChangeProfile B F E S) (scope : B → Prop)
    (hMenu : NamedMenu m a scope) (hNoCapacity : CapacityCalibrationFails m scope)
    (hNoWithout : WithoutMatterCalibrationFails m scope) :
    ChangeProxyCalibration m a scope := by
  sorry

end TruthCore.Results.Aquinas.SummaTheologiae.Q14ReceptionFork
