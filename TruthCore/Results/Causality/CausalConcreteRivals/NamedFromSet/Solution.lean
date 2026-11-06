module

public import TruthCore.Causality.CausalConcreteRivalBoundary

@[expose] public section
namespace TruthCore.Results.Causality.CausalConcreteRivals.NamedFromSet
open TruthCore.Causality.CausalConcreteRivalBoundary
open TruthCore.Causality.CausalPowerConcreteness

/-- Analyst conditional obligation; original source readings and approved floor remain unchanged. -/
theorem namedFromSet (f : Frame) (h : SetCounter f) : NamedCases f := by
  exact Or.inl h

end TruthCore.Results.Causality.CausalConcreteRivals.NamedFromSet
