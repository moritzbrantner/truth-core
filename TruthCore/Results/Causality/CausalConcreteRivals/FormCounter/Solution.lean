module

public import TruthCore.Causality.CausalConcreteRivalBoundary

@[expose] public section
namespace TruthCore.Results.Causality.CausalConcreteRivals.FormCounter
open TruthCore.Causality.CausalConcreteRivalBoundary
open TruthCore.Causality.CausalPowerConcreteness

/-- Analyst conditional obligation; original source readings and approved floor remain unchanged. -/
theorem formCounter (f : Frame) (hCause : FormCause f) (hNoEsse : FormCausersNoEsse f) : FormCounter f := by
  obtain ⟨x, y, hx, hc⟩ := hCause
  exact ⟨x, y, hx, hNoEsse x y hx hc, hc⟩

end TruthCore.Results.Causality.CausalConcreteRivals.FormCounter
