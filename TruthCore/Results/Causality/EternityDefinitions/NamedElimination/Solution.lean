module

public import TruthCore.Causality.EternityDefinitionFork

@[expose] public section
namespace TruthCore.Results.Causality.EternityDefinitions.NamedElimination
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Causality.EternityDefinitionFork

/-- Frozen analyst consequence; no semantic calibration or actual-life premise adopted. -/
theorem namedElimination (f : Frame) (hCoverage : NamedCoverage f) (hNoEndless : EndlessDefinitionFails f) : BoethianDefinition f := by
  cases hCoverage with
  | inl h => exact h
  | inr h => exact False.elim (hNoEndless h)

end TruthCore.Results.Causality.EternityDefinitions.NamedElimination
