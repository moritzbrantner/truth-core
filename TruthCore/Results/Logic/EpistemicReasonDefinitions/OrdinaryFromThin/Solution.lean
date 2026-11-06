module

public import TruthCore.Logic.EpistemicReasonDefinitionFork

@[expose] public section

namespace TruthCore.Results.Logic.EpistemicReasonDefinitions.OrdinaryFromThin

open TruthCore.Logic TruthCore.Logic.EpistemicReasons
open TruthCore.Logic.EpistemicReasonDefinitionFork

/-- Frozen scoped obligation; no normative premise is established by choosing a calibration. -/
theorem ordinaryFromThin (f : Frame)
    (hThin : ThereAreEpistemicReasons f.Reason)
    (hPresentation : ConsiderationPresentation f)
    (hDefinition : OrdinaryDefinition f) :
    SomeOrdinaryReason f := by
  obtain ⟨a, p, hReason⟩ := hThin
  obtain ⟨r, hr⟩ := (hPresentation a p).mp hReason
  exact ⟨a, r, f.believe p, hr, (hDefinition a r (f.believe p)).mp hr⟩

end TruthCore.Results.Logic.EpistemicReasonDefinitions.OrdinaryFromThin
