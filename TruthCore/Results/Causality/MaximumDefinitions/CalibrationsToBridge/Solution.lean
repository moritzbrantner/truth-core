module

public import TruthCore.Causality.MaximumDefinitionFork

@[expose] public section
namespace TruthCore.Results.Causality.MaximumDefinitions.CalibrationsToBridge
open TruthCore.Causality.MaximumDefinitionFork

/-- Frozen analyst calibration consequence; no meaning is selected. -/
theorem calibrationsToBridge {Degree : Type} [Preorder Degree] (f : Frame Degree)
    (hMaximal : MaximalDefinition f) (hGreatest : GreatestDefinition f) : MaximalToGreatest f := by
  intro m hm
  exact (hGreatest m).mp ((hMaximal m).mpr hm)

end TruthCore.Results.Causality.MaximumDefinitions.CalibrationsToBridge
