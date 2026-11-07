import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question14.ReceptionDefinitionFork

namespace TruthCore.Results.Aquinas.SummaTheologiae.Q14ReceptionFork
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.SummaTheologiae.FormReception
open TruthCore.Latin.Aquinas.SummaTheologiae.Q14ReceptionFork

theorem definitionFork {B F E S : Type} (m : Model B F)
    (a : ChangeProfile B F E S) (scope : B → Prop)
    (hEM : TruthCore.Logic.ExcludedMiddle) : DefinitionFork m a scope := by
  sorry

end TruthCore.Results.Aquinas.SummaTheologiae.Q14ReceptionFork
