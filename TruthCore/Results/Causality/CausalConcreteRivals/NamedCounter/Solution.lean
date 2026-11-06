module

public import TruthCore.Causality.CausalConcreteRivalBoundary

@[expose] public section
namespace TruthCore.Results.Causality.CausalConcreteRivals.NamedCounter
open TruthCore.Causality.CausalConcreteRivalBoundary
open TruthCore.Causality.CausalPowerConcreteness

/-- Analyst conditional obligation; original source readings and approved floor remain unchanged. -/
theorem namedCounter (f : Frame) (h : NamedCases f) : SelectedCounter f := by
  rcases h with ⟨x, y, _, hn, hc⟩ | ⟨x, y, _, hn, hc⟩ | ⟨x, y, _, _, hn, hc⟩
  all_goals exact ⟨x, hn, Or.inr ⟨y, hc⟩⟩

end TruthCore.Results.Causality.CausalConcreteRivals.NamedCounter
