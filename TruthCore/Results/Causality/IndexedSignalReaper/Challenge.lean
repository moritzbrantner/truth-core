import TruthCore.Causality.IndexedSignalReaper

namespace TruthCore.Results.Causality.IndexedSignalReaper
open TruthCore.Causality
open TruthCore.Causality.IndexedSignalProvenance
open TruthCore.Causality.IndexedSignalReaper

/-- Derive the existing action law from four explicit local interfaces;
neither global provenance nor the action law is an input. -/
theorem firingLaw (signal : Nat → Option Nat) (issued : Nat → Prop)
    (hBound : IndexAdmissible signal)
    (hTrigger : PositiveTrigger signal issued)
    (hEmit : Emission signal issued)
    (hForward : Forwarding signal) : GrimReaperLaw issued := by
  sorry

/-- Four same-carrier omissions retain all three other local rules. -/
theorem controls : TruthCore.Causality.IndexedSignalReaper.Controls := by
  sorry

end TruthCore.Results.Causality.IndexedSignalReaper
