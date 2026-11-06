module

public import TruthCore.Causality.CausalConcreteRivalBoundary

@[expose] public section
namespace TruthCore.Results.Causality.CausalConcreteRivals.OtherProjection
open TruthCore.Causality.CausalConcreteRivalBoundary

/-- Explicit graph connection from the relevant remainder to the selected countercase. -/
theorem otherProjection (f : Frame) (h : OtherCounter f) : SelectedCounter f := by
  exact h.1

end TruthCore.Results.Causality.CausalConcreteRivals.OtherProjection
