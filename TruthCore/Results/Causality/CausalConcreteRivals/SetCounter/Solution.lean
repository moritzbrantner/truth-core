module

public import TruthCore.Causality.CausalConcreteRivalBoundary

@[expose] public section
namespace TruthCore.Results.Causality.CausalConcreteRivals.SetCounter
open TruthCore.Causality.CausalConcreteRivalBoundary
open TruthCore.Causality.CausalPowerConcreteness

/-- Analyst conditional obligation; original source readings and approved floor remain unchanged. -/
theorem setCounter (f : Frame) (hCause : SetCause f) (hNoEsse : SetCausersNoEsse f) : SetCounter f := by
  obtain ⟨x, y, hx, hc⟩ := hCause
  exact ⟨x, y, hx, hNoEsse x y hx hc, hc⟩

end TruthCore.Results.Causality.CausalConcreteRivals.SetCounter
