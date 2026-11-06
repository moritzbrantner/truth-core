module

public import TruthCore.Causality.ComposerTemporalDefinitionFork

@[expose] public section
namespace TruthCore.Results.Causality.ComposerTemporalDefinitions.CurrentCalibration
open TruthCore.Causality.ComposerTemporalDefinitionFork

/-- Frozen analyst obligation; no calibration is adopted. -/
theorem currentCalibration (f : Frame) (hDef : CurrentDefinition f) (hComposer : AttributedComposer f) : CurrentComposer f := by
  intro c a b x hu
  obtain ⟨r, hr⟩ := hComposer c a b x hu
  exact ⟨r, (hDef c x r).mp hr⟩

end TruthCore.Results.Causality.ComposerTemporalDefinitions.CurrentCalibration
