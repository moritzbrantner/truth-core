module

public import TruthCore.Causality.CausalConcreteRivalBoundary

@[expose] public section
namespace TruthCore.Results.Causality.CausalConcreteRivals.NamedFromForm
open TruthCore.Causality.CausalConcreteRivalBoundary
open TruthCore.Causality.CausalPowerConcreteness

/-- Analyst conditional obligation; original source readings and approved floor remain unchanged. -/
theorem namedFromForm (f : Frame) (h : FormCounter f) : NamedCases f := by
  exact Or.inr (Or.inl h)

end TruthCore.Results.Causality.CausalConcreteRivals.NamedFromForm
