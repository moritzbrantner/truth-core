module

public import TruthCore.Logic.EpistemicReasonDefinitionFork

@[expose] public section

namespace TruthCore.Results.Logic.EpistemicReasonDefinitions.IndependentFromThin

open TruthCore.Logic TruthCore.Logic.EpistemicReasons
open TruthCore.Logic.EpistemicReasonDefinitionFork

/-- Frozen scoped obligation; no normative premise is established by choosing a calibration. -/
theorem independentFromThin (f : Frame)
    (hThin : ThereAreEpistemicReasons f.Reason)
    (hPresentation : ConsiderationPresentation f)
    (hDefinition : PreferenceIndependentDefinition f) :
    SomePreferenceIndependentReason f := by
  obtain ⟨a, p, hReason⟩ := hThin
  obtain ⟨r, hr⟩ := (hPresentation a p).mp hReason
  obtain ⟨hRole, hForce⟩ := (hDefinition a r (f.believe p)).mp hr
  exact ⟨a, r, f.believe p, ⟨hr, hRole⟩, hForce⟩

end TruthCore.Results.Logic.EpistemicReasonDefinitions.IndependentFromThin
