module

public import TruthCore.Results.Causality.ComposerTemporalDefinitions.NamedElimination.Solution

@[expose] public section

namespace TruthCore.Results.Causality.ComposerTemporalDefinitions.NamedElimination.Bound
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article7Uniting
open TruthCore.Causality.ComposerTemporalDefinitionFork

/-- Frozen analyst obligation; no calibration is adopted. -/
theorem namedElimination (f : Frame) (hCoverage : NamedCoverage f) (hNotCurrent : CurrentDefinitionFails f) : TemporalDefinition f := by
  exact TruthCore.Results.Causality.ComposerTemporalDefinitions.NamedElimination.namedElimination f hCoverage hNotCurrent

end TruthCore.Results.Causality.ComposerTemporalDefinitions.NamedElimination.Bound
