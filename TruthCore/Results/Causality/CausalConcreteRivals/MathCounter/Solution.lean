module

public import TruthCore.Causality.CausalConcreteRivalBoundary

@[expose] public section
namespace TruthCore.Results.Causality.CausalConcreteRivals.MathCounter
open TruthCore.Causality.CausalConcreteRivalBoundary
open TruthCore.Causality.CausalPowerConcreteness

/-- Analyst conditional obligation; original source readings and approved floor remain unchanged. -/
theorem mathCounter (f : Frame) (hRelevant : MathRelevance f)
    (hProductive : RelevanceIsProductive f) (hNoEsse : RelevantFactsNoEsse f) : MathCounter f := by
  obtain ⟨x, y, hx, hr⟩ := hRelevant
  exact ⟨x, y, hx, hr, hNoEsse x y hx hr, hProductive x y hx hr⟩

end TruthCore.Results.Causality.CausalConcreteRivals.MathCounter
