import TruthCore.Logic.EpistemicReasonDefinitionFork

namespace TruthCore.Results.Logic.EpistemicReasonDefinitions.OrdinaryFromThin

open TruthCore.Logic TruthCore.Logic.EpistemicReasons
open TruthCore.Logic.EpistemicReasonDefinitionFork

/-- Frozen scoped obligation; no normative premise is established by choosing a calibration. -/
theorem ordinaryFromThin (f : Frame)
    (hThin : ThereAreEpistemicReasons f.Reason)
    (hPresentation : ConsiderationPresentation f)
    (hDefinition : OrdinaryDefinition f) :
    SomeOrdinaryReason f := by
  sorry

end TruthCore.Results.Logic.EpistemicReasonDefinitions.OrdinaryFromThin
