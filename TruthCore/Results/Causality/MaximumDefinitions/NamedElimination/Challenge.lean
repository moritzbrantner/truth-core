import TruthCore.Causality.MaximumDefinitionFork

namespace TruthCore.Results.Causality.MaximumDefinitions.NamedElimination
open TruthCore.Causality.MaximumDefinitionFork

/-- Frozen analyst calibration consequence; no meaning is selected. -/
theorem namedElimination {Degree : Type} [Preorder Degree] (f : Frame Degree)
    (hCoverage : NamedCoverage f) (hNotMaximal : MaximalDefinitionFails f)
    (hNotStrict : StrictDefinitionFails f) : GreatestDefinition f := by
  sorry

end TruthCore.Results.Causality.MaximumDefinitions.NamedElimination
