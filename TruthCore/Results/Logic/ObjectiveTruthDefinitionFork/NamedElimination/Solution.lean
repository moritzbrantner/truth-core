module

public import TruthCore.Logic.ObjectiveTruthDefinitionFork

@[expose] public section
namespace TruthCore.Results.Logic.ObjectiveTruthDefinitionFork.NamedElimination
open TruthCore.Logic
open TruthCore.Logic.ObjectiveTruthDefinitionFork

theorem namedElimination (f : Frame) (hCoverage : NamedCoverage f)
    (hNotInvariant : NotInvariantOnlyDefinition f)
    (hNotActual : NotActualTruthOnlyDefinition f) : ActualStableDefinition f := by
  cases hCoverage with
  | inl h => exact h
  | inr h =>
    cases h with
    | inl h => exact False.elim (hNotInvariant h)
    | inr h => exact False.elim (hNotActual h)

end TruthCore.Results.Logic.ObjectiveTruthDefinitionFork.NamedElimination
