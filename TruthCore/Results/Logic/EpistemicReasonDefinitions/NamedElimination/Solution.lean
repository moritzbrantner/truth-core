module

public import TruthCore.Logic.EpistemicReasonDefinitionFork
public import TruthCore.Results.Logic.EpistemicReasonDefinitions.OrdinaryFromThin.Solution
public import TruthCore.Results.Logic.EpistemicReasonDefinitions.IndependentFromThin.Solution
public import TruthCore.Results.Logic.EpistemicReasonDefinitions.IndependentStrength.Solution

@[expose] public section

namespace TruthCore.Results.Logic.EpistemicReasonDefinitions.NamedElimination

open TruthCore.Logic TruthCore.Logic.EpistemicReasons
open TruthCore.Logic.EpistemicReasonDefinitionFork

/-- Frozen scoped obligation; no normative premise is established by choosing a calibration. -/
theorem namedDefinitionElimination (f : Frame)
    (hThin : ThereAreEpistemicReasons f.Reason)
    (hPresentation : ConsiderationPresentation f)
    (hCoverage : NamedDefinitionCoverage f)
    (hNotProduction : ProductionDefinitionFails f)
    (hNotReward : RewardDefinitionFails f) :
    SomeOrdinaryReason f := by
  cases hCoverage with
  | inl hOrdinary =>
    exact TruthCore.Results.Logic.EpistemicReasonDefinitions.OrdinaryFromThin.ordinaryFromThin
      f hThin hPresentation hOrdinary
  | inr hRest =>
    cases hRest with
    | inl hIndependent =>
      exact TruthCore.Results.Logic.EpistemicReasonDefinitions.IndependentStrength.independentStrengthensOrdinary
        f (TruthCore.Results.Logic.EpistemicReasonDefinitions.IndependentFromThin.independentFromThin
          f hThin hPresentation hIndependent)
    | inr hOther =>
      cases hOther with
      | inl hProduction => exact False.elim (hNotProduction hProduction)
      | inr hReward => exact False.elim (hNotReward hReward)

end TruthCore.Results.Logic.EpistemicReasonDefinitions.NamedElimination
