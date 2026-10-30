import TruthCore.Epistemology.UltimateExplanation
import TruthCore.Results.Causality.ChainInstantiation.Solution

/-! #743. Analyst law-identification test, not a modal or epistemic theory.
Each time-dependent rule determines one full signal. A history explicitly
represents one present state-bearer at every time. These mathematical witnesses
are not actual concreta; real applicability and warrant remain OPEN. -/
namespace TruthCore.Explanation.LawActuality
open TruthCore.Epistemology.UltimateExplanation
open TruthCore.Modern.Hume.Induction
open TruthCore.Explanation.HistorySelection
open TruthCore.Modal.TemporalHistory TruthCore.Modal.HistoryContrastive

/-- Two laws share n+1 initial true readings, then prescribe b forever.
This parameter is a state value, not an adequacy/actuality flag. -/
def signal (n : Nat) (b : Bool) : Trace := fun t => if t < n+1 then true else b

def law (n : Nat) (b : Bool) : Profile :=
  ⟨true, fun t _ next => next = signal n b (t+1)⟩

/-- Both state-bearers are candidates; exactly the signal's state is present.
Existence is interpreted at now=0. No causal relation is postulated. -/
def realized (n : Nat) : History Bool Bool Nat where
  ontic := { frame := ⟨fun _ _ => True⟩
             ExistsAt := fun w x => x = signal n w 0
             Causes := fun _ _ _ => False }
  IsAt := fun w x t => x = signal n w t
  now := 0

/-- Readout is an exact state measurement. All value propositions at recorded
indices are admitted, so the result is not caused by dropping false readings. -/
def readings (n : Nat) (w : Bool) (r : Nat × Bool) : Prop := signal n w r.1 = r.2

def window (n : Nat) (r : Nat × Bool) : Prop := r.1 < n+1

/-- An arbitrary total deterministic estimator invariant under the entire
recorded prefix, not just persistence, computability or a finite hypothesis list.
Exact uniform identification is stronger than fallible epistemic justification. -/
def UsesRecord (n : Nat) (estimate : Trace → Bool) : Prop :=
  ∀ f g, (∀ i, i < n+1 → f i = g i) → estimate f = estimate g

def Identifies (n : Nat) (estimate : Trace → Bool) : Prop :=
  ∀ b, estimate (signal n b) = b

/-- Closed mathematical discriminator: each of two deterministic laws has a
unique complete solution and a coherent populated realization, but no arbitrary
record-only estimator identifies both, and #736's entailing selector fails at
either designation. This asserts no metaphysical possibility or entitlement. -/
def Certificate : Prop := ∀ n,
  (∀ b, Deterministic (law n b) ∧ Follows (law n b) (signal n b) ∧
    ∀ f, Follows (law n b) f → f = signal n b) ∧
  (CoherentAtNow (realized n) ∧
    ∀ w t, ∃ x, (realized n).IsAt w x t ∧
      ∀ y, (realized n).IsAt w y t → y = x) ∧
  (∀ estimate, UsesRecord n estimate → ¬ Identifies n estimate) ∧
  (∀ a, ¬ Determines (realized n) (readings n) (window n) a ∧
    ¬ ∃ p, EvidenceOnly (readings n) (window n) p ∧ Selects (realized n) p a)

/-- Remove recorded-prefix restriction: the first unobserved reading identifies
both laws and provides whole-history determination. Remove the competing law:
a constant estimator identifies the retained true-law candidate. These are
positive controls, not claims that these extra inputs are actually available.
The old #704 control separately keeps the same candidate domain and transmission
equations with empty/full presence. Here empty state presence likewise cannot
alter unique formal solutions: law satisfaction does not reference population. -/
def emptyRealization (n : Nat) : History Bool Bool Nat :=
  { realized n with ontic := { (realized n).ontic with ExistsAt := fun _ _ => False }
                    IsAt := fun _ _ _ => False }

def Omissions : Prop :=
  (∀ n, Identifies n (fun f => f (n+1)) ∧
    ¬ UsesRecord n (fun f => f (n+1)) ∧
    (∀ a, Determines (realized n) (readings n) (fun _ => True) a) ∧
    (UsesRecord n (fun _ => true) ∧ (fun _ : Trace => true) (signal n true) = true) ∧
    CoherentAtNow (emptyRealization n) ∧
    (¬ ∃ w x t, (emptyRealization n).IsAt w x t) ∧
    (∀ b, ∃! f, Follows (law n b) f)) ∧
  TruthCore.Causality.ChainInstantiation.Controls
end TruthCore.Explanation.LawActuality
