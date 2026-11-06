module

public import TruthCore.Alternatives.NaturalReasonHorizon

@[expose] public section

namespace TruthCore.Results.Alternatives.NaturalReasonHorizon.Projection

open TruthCore.Alternatives.Fideism
open TruthCore.Alternatives.NaturalReasonHorizon

/-- Exact profile consequence; no descriptive horizon is silently negated. -/
theorem uniformRejectionIncludesShared (P : Practice) (hBoth : UniformNaturalReasonRejected P) : SharedNaturalReasonRejected P := by
  exact hBoth.1

end TruthCore.Results.Alternatives.NaturalReasonHorizon.Projection
