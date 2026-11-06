module

public import TruthCore.Logic.EpistemicReasonDefinitionFork

@[expose] public section

namespace TruthCore.Results.Logic.EpistemicReasonDefinitions.IndependentStrength

open TruthCore.Logic TruthCore.Logic.EpistemicReasons
open TruthCore.Logic.EpistemicReasonDefinitionFork

/-- Frozen scoped obligation; no normative premise is established by choosing a calibration. -/
theorem independentStrengthensOrdinary (f : Frame)
    (hIndependent : SomePreferenceIndependentReason f) :
    SomeOrdinaryReason f := by
  obtain ⟨a, r, t, hOrdinary, _⟩ := hIndependent
  exact ⟨a, r, t, hOrdinary⟩

end TruthCore.Results.Logic.EpistemicReasonDefinitions.IndependentStrength
