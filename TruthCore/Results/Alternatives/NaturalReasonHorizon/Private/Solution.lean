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
  intro hShared
  obtain ⟨m, hNatural⟩ := hWitness
  exact hNever m hNatural (hShared m hNatural)

end TruthCore.Results.Alternatives.NaturalReasonHorizon.Private
