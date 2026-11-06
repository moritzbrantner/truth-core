module

public import TruthCore.Logic.ObjectiveTruthDefinitionFork
public import TruthCore.Results.Logic.ObjectiveTruthDefinitionFork.Controls.Solution

@[expose] public section
namespace TruthCore.Results.Logic.ObjectiveTruthDefinitionFork.BridgeOmission
open TruthCore.Logic.ObjectiveTruthDefinitionFork
open TruthCore.Results.Logic.ObjectiveTruthDefinitionFork.Controls

theorem bridgeOmission : BridgeOmissionControl := by
  refine ⟨invariantCalibration, ?_, ?_, ?_, rfl, Or.inr rfl, ?_, ?_⟩
  · intro s h
    cases h
    intro hFalse
    exact hFalse
  · intro s h
    exact h
  · intro s h
    exact h
  · intro h
    exact h
  · intro h
    exact h Content.stableFalse (Or.inr rfl)

end TruthCore.Results.Logic.ObjectiveTruthDefinitionFork.BridgeOmission
