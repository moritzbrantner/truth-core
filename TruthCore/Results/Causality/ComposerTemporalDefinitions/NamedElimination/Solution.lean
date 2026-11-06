module

public import TruthCore.Causality.ComposerTemporalDefinitionFork

@[expose] public section
namespace TruthCore.Results.Causality.ComposerTemporalDefinitions.NamedElimination
open TruthCore.Causality.ComposerTemporalDefinitionFork

/-- Frozen analyst obligation; no calibration is adopted. -/
theorem namedElimination (f : Frame) (hCoverage : NamedCoverage f) (hNotCurrent : ¬ CurrentDefinition f) : TemporalDefinition f := by
  cases hCoverage with
  | inl h => exact False.elim (hNotCurrent h)
  | inr h => exact h

end TruthCore.Results.Causality.ComposerTemporalDefinitions.NamedElimination
