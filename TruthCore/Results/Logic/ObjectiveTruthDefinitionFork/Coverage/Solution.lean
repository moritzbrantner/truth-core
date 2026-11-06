module

public import TruthCore.Logic.ObjectiveTruthDefinitionFork

@[expose] public section
namespace TruthCore.Results.Logic.ObjectiveTruthDefinitionFork.Coverage
open TruthCore.Logic
open TruthCore.Logic.ObjectiveTruthDefinitionFork

theorem definitionFork (hEM : ExcludedMiddle) : DefinitionFork := by
  intro f
  cases hEM (ActualStableDefinition f) with
  | inl h => exact Or.inl h
  | inr hNotProfile =>
    cases hEM (InvariantOnlyDefinition f) with
    | inl h => exact Or.inr (Or.inl h)
    | inr hNotInvariant =>
      cases hEM (ActualTruthOnlyDefinition f) with
      | inl h => exact Or.inr (Or.inr (Or.inl h))
      | inr hNotActual =>
        exact Or.inr (Or.inr (Or.inr ⟨hNotProfile, hNotInvariant, hNotActual⟩))

end TruthCore.Results.Logic.ObjectiveTruthDefinitionFork.Coverage
