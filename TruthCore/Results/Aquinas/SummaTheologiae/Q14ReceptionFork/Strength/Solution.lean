module

public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question14.ReceptionDefinitionFork

@[expose] public section
namespace TruthCore.Results.Aquinas.SummaTheologiae.Q14ReceptionFork
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.SummaTheologiae.FormReception
open TruthCore.Latin.Aquinas.SummaTheologiae.Q14ReceptionFork

theorem foreignCapacityOfWithoutMatter {B F : Type} (m : Model B F) (x : B)
    (h : WithoutMatterCapacity m x) : ForeignFormCapacity m x := by
  obtain ⟨f, hf, hm⟩ := h
  exact ⟨f, hf, .withoutMatter, hm⟩

end TruthCore.Results.Aquinas.SummaTheologiae.Q14ReceptionFork
