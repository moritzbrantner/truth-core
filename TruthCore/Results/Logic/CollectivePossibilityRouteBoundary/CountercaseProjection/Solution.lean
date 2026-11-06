module

public import TruthCore.Logic.CollectivePossibilityRouteBoundary

@[expose] public section
namespace TruthCore.Results.Logic.CollectivePossibilityRouteBoundary.CountercaseProjection
open TruthCore.Logic.CollectivePossibilityRouteBoundary

/-- The actual fork countercase negates the same collective premise. -/
theorem countercaseProjection (f : Frame) (h : Countercase f) : CollectiveFails f := by
  intro hc
  exact h.2 (hc h.1)

end TruthCore.Results.Logic.CollectivePossibilityRouteBoundary.CountercaseProjection
