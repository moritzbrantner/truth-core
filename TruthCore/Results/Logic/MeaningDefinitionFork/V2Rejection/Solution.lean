module

public import TruthCore.Logic.MeaningDefinitionFork
public import TruthCore.Results.Logic.Verificationism.Ayer1936Trivial.Solution

@[expose] public section
namespace TruthCore.Results.Logic.MeaningDefinitionFork.V2Rejection
open TruthCore.Logic.Verificationism
open TruthCore.Logic.MeaningDefinitionFork
theorem v2Rejection {L : Language} (F : Frame L) (meaningful scope : L.Sentence → Prop)
    (hTarget : V2ExcludedTarget F meaningful scope) : ¬ V2Definition F meaningful scope := by
  intro hDefinition
  obtain ⟨m, o, hm, hNot, ho, hIndependent⟩ := hTarget
  have admitted := TruthCore.Results.Logic.Verificationism.Ayer1936Trivial.ayer1936CriterionTrivial
    L F o m ho hIndependent
  exact hNot ((hDefinition m hm).mpr (Or.inr admitted))

end TruthCore.Results.Logic.MeaningDefinitionFork.V2Rejection
