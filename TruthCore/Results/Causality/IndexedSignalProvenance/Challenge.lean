import TruthCore.Causality.IndexedSignalProvenance

namespace TruthCore.Results.Causality.IndexedSignalProvenance
open TruthCore.Causality.IndexedSignalProvenance

/-- Finite code bounds and unchanged local forwarding suffice for actual
issuance in the stipulated role, without global chain well-foundedness. -/
theorem provenance (signal : Nat → Option Nat) (issued : Nat → Prop)
    (hConserve : LocalConservation signal issued)
    (hBound : IndexAdmissible signal) : GlobalProvenance signal issued := by
  sorry

/-- Delete either local interface, and retain the other on the same Nat
carrier. A quiet model also prevents reading a firing law into the premises. -/
theorem controls : Controls := by
  sorry

end TruthCore.Results.Causality.IndexedSignalProvenance
