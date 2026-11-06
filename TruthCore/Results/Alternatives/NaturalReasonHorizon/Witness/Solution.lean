module

public import TruthCore.Alternatives.NaturalReasonHorizon

@[expose] public section

namespace TruthCore.Results.Alternatives.NaturalReasonHorizon.Witness

open TruthCore.Alternatives.Fideism
open TruthCore.Alternatives.NaturalReasonHorizon

/-- Exact profile consequence; no descriptive horizon is silently negated. -/
theorem councilSuppliesNaturalMove (P : Practice)
    (hCouncil : CouncilDefinesNaturalKnowabilityReading P) : NaturalKnowabilityMoveExists P := by
  obtain ⟨m, hNatural, _⟩ := hCouncil
  exact ⟨m, hNatural⟩

end TruthCore.Results.Alternatives.NaturalReasonHorizon.Witness
