import TruthCore.Logic.EpistemicReasonDefinitionFork

namespace TruthCore.Results.Logic.EpistemicReasonDefinitions.IndependentStrength

open TruthCore.Logic TruthCore.Logic.EpistemicReasons
open TruthCore.Logic.EpistemicReasonDefinitionFork

/-- Frozen scoped obligation; no normative premise is established by choosing a calibration. -/
theorem independentStrengthensOrdinary (f : Frame)
    (hIndependent : SomePreferenceIndependentReason f) :
    SomeOrdinaryReason f := by
  sorry

end TruthCore.Results.Logic.EpistemicReasonDefinitions.IndependentStrength
