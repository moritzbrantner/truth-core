module

public import TruthCore.Alternatives.NaturalReasonHorizon

@[expose] public section

namespace TruthCore.Results.Alternatives.NaturalReasonHorizon.Mixed

open TruthCore.Alternatives.Fideism
open TruthCore.Alternatives.NaturalReasonHorizon

/-- Exact profile consequence; no descriptive horizon is silently negated. -/
theorem mixedRejectsUniform (P : Practice) (hMixed : MixedNaturalReason P) : UniformNaturalReasonRejected P := by
  obtain ⟨⟨m, hNaturalM, hSharedM⟩, n, hNaturalN, hNotSharedN⟩ := hMixed
  constructor
  · intro hShared; exact hNotSharedN (hShared n hNaturalN)
  · intro hNever; exact hNever m hNaturalM hSharedM

end TruthCore.Results.Alternatives.NaturalReasonHorizon.Mixed
