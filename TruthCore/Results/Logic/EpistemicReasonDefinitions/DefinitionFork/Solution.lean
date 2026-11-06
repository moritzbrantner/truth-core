module

public import TruthCore.Logic.EpistemicReasonDefinitionFork

@[expose] public section

namespace TruthCore.Results.Logic.EpistemicReasonDefinitions.DefinitionFork

open TruthCore.Logic TruthCore.Logic.EpistemicReasons
open TruthCore.Logic.EpistemicReasonDefinitionFork

/-- Frozen scoped obligation; no normative premise is established by choosing a calibration. -/
theorem definitionFork (hEM : ExcludedMiddle) :
    DefinitionFork := by
  intro f
  cases hEM (OrdinaryDefinition f) with
  | inl h => exact Or.inl (Or.inl h)
  | inr hOrdinary =>
    cases hEM (PreferenceIndependentDefinition f) with
    | inl h => exact Or.inl (Or.inr (Or.inl h))
    | inr hIndependent =>
      cases hEM (ProductionDefinition f) with
      | inl h => exact Or.inl (Or.inr (Or.inr (Or.inl h)))
      | inr hProduction =>
        cases hEM (RewardDefinition f) with
        | inl h => exact Or.inl (Or.inr (Or.inr (Or.inr h)))
        | inr hReward => exact Or.inr ⟨hOrdinary, hIndependent, hProduction, hReward⟩

end TruthCore.Results.Logic.EpistemicReasonDefinitions.DefinitionFork
