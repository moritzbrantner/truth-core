module

public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question14.ReceptionDefinitionFork

@[expose] public section
namespace TruthCore.Results.Aquinas.SummaTheologiae.Q14ReceptionFork
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.SummaTheologiae.FormReception
open TruthCore.Latin.Aquinas.SummaTheologiae.Q14ReceptionFork

theorem modeElimination {B F : Type} (m : Model B F) (x : B)
    (hAvailable : ForeignFormCapacity m x) (hNoMatter : NoMaterialReception m x) :
    WithoutMatterCapacity m x := by
  exact FormReception.availableFormWithoutMatter m x hAvailable hNoMatter

end TruthCore.Results.Aquinas.SummaTheologiae.Q14ReceptionFork
