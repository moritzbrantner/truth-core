module

public import TruthCore.Results.Causality.ComposerTemporalDefinitions.CurrentCalibration.Solution

@[expose] public section

namespace TruthCore.Results.Causality.ComposerTemporalDefinitions.CurrentCalibration.Bound
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article7Uniting
open TruthCore.Causality.ComposerTemporalDefinitionFork

/-- Frozen analyst obligation; no calibration is adopted. -/
theorem currentCalibration (f : Frame) (hDef : CurrentDefinition f) (hComposer : AttributedComposer f) : UnitingCauseIsEfficientCauseReading f.Unites (Current f) := by
  exact TruthCore.Results.Causality.ComposerTemporalDefinitions.CurrentCalibration.currentCalibration f hDef hComposer

end TruthCore.Results.Causality.ComposerTemporalDefinitions.CurrentCalibration.Bound
