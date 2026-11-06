module

public import TruthCore.Logic.MeaningDefinitionFork
public import TruthCore.Results.Logic.Verificationism.Ayer1946Closure.Solution

@[expose] public section
namespace TruthCore.Results.Logic.MeaningDefinitionFork.V3Rejection
open TruthCore.Logic.Verificationism
open TruthCore.Logic.MeaningDefinitionFork
theorem v3Rejection {L : Language} (F : Frame L) (meaningful : L.Sentence → Prop)
    (hClosed : MeaningClosedUnderNegation L meaningful)
    (hObservations : ∃ o₁ o₂ o₃, ChurchObservations F o₁ o₂ o₃)
    (hExcluded : ExcludedNegation meaningful) : ¬ V3Definition F meaningful GlobalScope := by
  intro hDefinition
  apply TruthCore.Results.Logic.Verificationism.Ayer1946Closure.ayer1946ExcludesANegationFails
    F meaningful hClosed
  exact ⟨fun s => hDefinition s True.intro, hObservations, hExcluded⟩

end TruthCore.Results.Logic.MeaningDefinitionFork.V3Rejection
