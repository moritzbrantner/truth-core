module

public import TruthCore.Causality.MaximumDefinitionFork

@[expose] public section
namespace TruthCore.Results.Causality.MaximumDefinitions.NamedElimination
open TruthCore.Causality.MaximumDefinitionFork

/-- Frozen analyst calibration consequence; no meaning is selected. -/
theorem namedElimination {Degree : Type} [Preorder Degree] (f : Frame Degree)
    (hCoverage : NamedCoverage f) (hNotMaximal : MaximalDefinitionFails f)
    (hNotStrict : StrictDefinitionFails f) : GreatestDefinition f := by
  cases hCoverage with
  | inl h => exact False.elim (hNotMaximal h)
  | inr h =>
    cases h with
    | inl h => exact h
    | inr h => exact False.elim (hNotStrict h)

end TruthCore.Results.Causality.MaximumDefinitions.NamedElimination
