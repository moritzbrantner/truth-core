import TruthCore.Causality.IndexedSignalProvenance
import TruthCore.Causality.GrimReaper

/-! Analyst closed-channel interfaces motivated conditionally by the indexed
Placer create/maintain scenario, not attributed as its exact formalization.
Option Nat contains only absence or a finite indexed code. Applying this to
particles/signals requires exhaustive admitted codes, faithful detection and
closed inputs: malformed tokens and a limit-position particle are not silently
ruled out by physics. No world, causal power or existential ground is encoded. -/
namespace TruthCore.Causality.IndexedSignalReaper
open TruthCore.Causality.IndexedSignalProvenance

/-- Positive trigger only: absence of an admitted upstream code requires
issuance in the stipulated role. Suppression with present input is not assumed. -/
def PositiveTrigger (signal : Nat → Option Nat) (issued : Nat → Prop) : Prop :=
  ∀ n, signal (n + 1) = none → issued n

/-- Issuance writes the station's own code to its output. This role does not
by itself certify physical production, or prevent incoming signals. -/
def Emission (signal : Nat → Option Nat) (issued : Nat → Prop) : Prop :=
  ∀ n, issued n → signal n = some n

/-- Every present upstream code is forwarded unchanged, with no erasure or
overwrite. This is complete local persistence, stronger than capacity to send. -/
def Forwarding (signal : Nat → Option Nat) : Prop :=
  ∀ n j, signal (n + 1) = some j → signal n = some j

/-- Every one-rule deletion admits a same-Nat interpretation retaining the
other three rules and falsifying the full Reaper law. These are mathematical
assignments only; no metaphysical realizability is certified. -/
def Controls : Prop :=
  (∃ signal issued, PositiveTrigger signal issued ∧ Emission signal issued ∧
    Forwarding signal ∧ ¬ IndexAdmissible signal ∧ ¬ GrimReaperLaw issued) ∧
  (∃ signal issued, IndexAdmissible signal ∧ Emission signal issued ∧
    Forwarding signal ∧ ¬ PositiveTrigger signal issued ∧ ¬ GrimReaperLaw issued) ∧
  (∃ signal issued, IndexAdmissible signal ∧ PositiveTrigger signal issued ∧
    Forwarding signal ∧ ¬ Emission signal issued ∧ ¬ GrimReaperLaw issued) ∧
  (∃ signal issued, IndexAdmissible signal ∧ PositiveTrigger signal issued ∧
    Emission signal issued ∧ ¬ Forwarding signal ∧ ¬ GrimReaperLaw issued)

end TruthCore.Causality.IndexedSignalReaper
