module

public import TruthCore.Causality.CausalConcreteRivalBoundary

@[expose] public section
namespace TruthCore.Results.Causality.CausalConcreteRivals.SetScopeStrength
open TruthCore.Causality.CausalConcreteRivalBoundary
open TruthCore.Causality.CausalPowerConcreteness

/-- Analyst conditional obligation; original source readings and approved floor remain unchanged. -/
theorem setScopeStrength (f : Frame) (h : AllSetsNoEsse f) : SetCausersNoEsse f := by
  exact fun x _ hx _ => h x hx

end TruthCore.Results.Causality.CausalConcreteRivals.SetScopeStrength
