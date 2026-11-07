module

public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question14.ReceptionDefinitionFork

@[expose] public section
namespace TruthCore.Results.Aquinas.SummaTheologiae.Q14ReceptionFork
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.SummaTheologiae.FormReception
open TruthCore.Latin.Aquinas.SummaTheologiae.Q14ReceptionFork

theorem definitionFork {B F E S : Type} (m : Model B F)
    (a : ChangeProfile B F E S) (scope : B → Prop)
    (hEM : TruthCore.Logic.ExcludedMiddle) : DefinitionFork m a scope := by
  rcases hEM (CapacityCalibration m scope) with h | h
  · exact Or.inl (Or.inl h)
  rcases hEM (WithoutMatterCalibration m scope) with h' | h'
  · exact Or.inl (Or.inr (Or.inl h'))
  rcases hEM (ChangeProxyCalibration m a scope) with h'' | h''
  · exact Or.inl (Or.inr (Or.inr h''))
  · exact Or.inr ⟨h, h', h''⟩

end TruthCore.Results.Aquinas.SummaTheologiae.Q14ReceptionFork
