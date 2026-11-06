module

public import TruthCore.Causality.CausalConcreteRivalBoundary

@[expose] public section
namespace TruthCore.Results.Causality.CausalConcreteRivals.CounterFailure
open TruthCore.Causality.CausalConcreteRivalBoundary
open TruthCore.Causality.CausalPowerConcreteness

/-- Analyst conditional obligation; original source readings and approved floor remain unchanged. -/
theorem counterFailure (f : Frame) (hCal : Calibration f) (h : SelectedCounter f) :
    OwnerFails f := by
  rintro hOwner
  obtain ⟨x, hx, hp | ⟨y, hc⟩⟩ := h
  · exact hx ((hCal x).mp (hOwner.1 x hp))
  · exact hx ((hCal x).mp (hOwner.2 x y hc))

end TruthCore.Results.Causality.CausalConcreteRivals.CounterFailure
