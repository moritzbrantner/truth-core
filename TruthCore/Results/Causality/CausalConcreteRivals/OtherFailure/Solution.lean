module

public import TruthCore.Causality.CausalConcreteRivalBoundary

@[expose] public section
namespace TruthCore.Results.Causality.CausalConcreteRivals.OtherFailure
open TruthCore.Causality.CausalConcreteRivalBoundary
open TruthCore.Causality.CausalPowerConcreteness

/-- Analyst conditional obligation; original source readings and approved floor remain unchanged. -/
theorem otherFailure (f : Frame) (h : OtherCounter f) : NamedCoverageFails f := by
  exact fun hCover => h.2 (hCover h.1)

end TruthCore.Results.Causality.CausalConcreteRivals.OtherFailure
