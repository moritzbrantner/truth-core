import TruthCore.Logic.EpistemicReasonDefinitionFork

namespace TruthCore.Results.Logic.EpistemicReasonDefinitions.IndependentFromThin

open TruthCore.Logic TruthCore.Logic.EpistemicReasons
open TruthCore.Logic.EpistemicReasonDefinitionFork

/-- Frozen scoped obligation; no normative premise is established by choosing a calibration. -/
theorem independentFromThin (f : Frame)
    (hThin : ThereAreEpistemicReasons f.Reason)
    (hPresentation : ConsiderationPresentation f)
    (hDefinition : PreferenceIndependentDefinition f) :
    SomePreferenceIndependentReason f := by
  sorry

end TruthCore.Results.Logic.EpistemicReasonDefinitions.IndependentFromThin
