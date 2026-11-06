module

public import TruthCore.Alternatives.NaturalReasonHorizon

@[expose] public section

namespace TruthCore.Results.Alternatives.NaturalReasonHorizon.Private

open TruthCore.Alternatives.Fideism
open TruthCore.Alternatives.NaturalReasonHorizon

/-- Exact profile consequence; no descriptive horizon is silently negated. -/
theorem nonsharedRejectsShared (P : Practice)
    (hNever : NaturalReasonNeverShared P)
    (hWitness : NaturalKnowabilityMoveExists P) : SharedNaturalReasonRejected P := by
  sorry

end TruthCore.Results.Alternatives.NaturalReasonHorizon.Private
