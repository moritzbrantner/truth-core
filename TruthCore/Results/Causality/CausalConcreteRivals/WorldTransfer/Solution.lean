module

public import TruthCore.Causality.CausalConcreteRivalBoundary

@[expose] public section
namespace TruthCore.Results.Causality.CausalConcreteRivals.WorldTransfer
open TruthCore.Causality.CausalConcreteRivalBoundary
open TruthCore.Causality.CausalPowerConcreteness

/-- Analyst conditional obligation; original source readings and approved floor remain unchanged. -/
theorem worldTransfer (f : Frame) (h : SuppliedWorldCounter f) (hWorld : CounterWorldIsSelected f) : SelectedCounter f := by
  unfold SuppliedWorldCounter at h
  unfold CounterWorldIsSelected at hWorld
  unfold SelectedCounter
  rw [hWorld] at h
  exact h

end TruthCore.Results.Causality.CausalConcreteRivals.WorldTransfer
