import TruthCore.Results.Modern.Hume.Induction.Solution
import TruthCore.Results.Modern.Hume.Regularity.Solution
import TruthCore.Results.Explanation.HistorySelection.Solution

/-! #737: bounded predictive/decision discriminator. Histories, temporal causes
and grounds reuse Hume's existing interfaces. Exact truth over an evidence cell
is deliberately stronger than fallible reliability, and is not defined as
justification. The additional normative entitlement bridge remains OPEN.
-/
namespace TruthCore.Epistemology.UltimateExplanation
open TruthCore.Modern.Hume.Induction
open TruthCore.Modern.Hume.Regularity

/-- A supplied local transition profile and initial condition. Actual lawhood,
causal efficacy, availability to an agent and ultimate explanation are separate
application obligations. Time-dependent rules are allowed. -/
structure Profile where
  initial : Bool
  step : Nat → Bool → Bool → Prop

/-- Satisfaction at every time, not observation or justified belief in a law. -/
def Follows (p : Profile) (f : Trace) : Prop :=
  f 0 = p.initial ∧ ∀ t, p.step t (f t) (f (t+1))

/-- Alternatives satisfying the supplied profile and the entire observed prefix
through n inclusive. No metaphysical possibility or chance measure is asserted. -/
def Cell (p : Profile) (observed : Trace) (n : Nat) (f : Trace) : Prop :=
  Follows p f ∧ ∀ i, i < n+1 → f i = observed i

/-- A persistence forecast uses only the last observed value, not a ground oracle. -/
def forecast (observed : Trace) (n : Nat) : Bool := observed n

/-- Zero prediction error on every admitted continuation. This is an explicit
strong reliability test, not a definition or proof of normative warrant. -/
def Accurate (p : Profile) (observed : Trace) (n : Nat) : Prop :=
  ∀ f, Cell p observed n f → forecast observed n = f (n+1)

/-- At most one permitted successor for a fixed time and state. Existence and
access to the input are separate; determinism does not mean constant output. -/
def Deterministic (p : Profile) : Prop :=
  ∀ t a b c, p.step t a b → p.step t a c → b = c

/-- A copy profile versus a rule allowing any output after the observed window.
These are explicit analyst models, not historical theories of all laws. -/
def stable : Profile := ⟨true, fun _ a b => b = a⟩
def openFuture (n : Nat) : Profile :=
  ⟨true, fun t a b => t+1 < n+1 → b = a⟩
def on : Trace := fun _ => true

inductive Action where
  | safe | betTrue | betFalse
  deriving DecidableEq

/-- Ordinal, stipulated task payoff; no interpersonal or probability comparison.
A safe action achieves 1 regardless of the binary outcome; a correct bet 2,
a wrong bet 0. Real availability and values remain application obligations. -/
def payoff : Action → Bool → Nat
  | .safe, _ => 1
  | .betTrue, true | .betFalse, false => 2
  | _, _ => 0

/-- Outcome-wise optimality is a strong decision test; a satisficing action can
remain usable even when no action passes it. Neither is normative rationality
by definition. -/
def Optimal (p : Profile) (observed : Trace) (n : Nat) (a : Action) : Prop :=
  ∀ f, Cell p observed n f → ∀ b, payoff b (f (n+1)) ≤ payoff a (f (n+1))
def Safe (p : Profile) (observed : Trace) (n : Nat) (a : Action) : Prop :=
  ∀ f, Cell p observed n f → 1 ≤ payoff a (f (n+1))

/-- Complete certified comparison, including explicit populated evidence cells,
local law satisfaction and same-prediction grounding contrast. Scope's
GroundedTotality means a supplied relation has a ground, not an adequate or
necessary ultimate explanation. The final refinement shows how an extra local-law restriction genuinely
improves prediction. Its evidential/normative availability is not proved. -/
def Certificate : Prop :=
  TruthCore.Modern.Hume.Induction.Checks ∧
  TruthCore.Modern.Hume.Regularity.Checks ∧
  (LocalCausality brute ∧ ¬ GroundedTotality brute ∧
    LocalCausality grounded ∧ GroundedTotality grounded) ∧
  Deterministic stable ∧
  (∀ n, Cell stable on n on ∧ Accurate stable on n ∧
    Optimal stable on n .betTrue) ∧
  (∀ (scope : Scope) n, ¬ GroundedTotality scope →
    Cell stable on n on ∧ Accurate stable on n ∧ Optimal stable on n .betTrue) ∧
  (∀ n, Cell (openFuture n) on n on ∧
    Cell (openFuture n) on n (delayedFailure (n+1)) ∧
    ¬ Accurate (openFuture n) on n ∧
    Safe (openFuture n) on n .safe ∧
    ¬ (∃ a, Optimal (openFuture n) on n a)) ∧
  (∀ n, GroundedTotality grounded ∧ ¬ Accurate (openFuture n) on n) ∧
  (∀ n, Recorded on (n+1) ∧ Recorded (delayedFailure (n+1)) (n+1)) ∧
  (∀ n, (∀ f, Cell stable on n f → Cell (openFuture n) on n f) ∧
    (∃ f, Cell (openFuture n) on n f ∧ ¬ Cell stable on n f))

/-- Omitted premises: a false initial condition empties the cell and makes all
forecasts and actions vacuously pass; a grounded scope and a wrong method leave
prediction error. The toggle is deterministic, while the constant-on trace
does not follow it. -/
def Omissions : Prop :=
  (let impossible : Profile := ⟨false, stable.step⟩
   (¬ ∃ f, Cell impossible on 0 f) ∧ Accurate impossible on 0 ∧
     Optimal impossible on 0 .betFalse) ∧
  (GroundedTotality grounded ∧ Follows stable on ∧
    (false : Bool) ≠ on 1) ∧
  (let toggle : Profile := ⟨true, fun _ a b => b = !a⟩
   Deterministic toggle ∧ ¬ Follows toggle on)

end TruthCore.Epistemology.UltimateExplanation

namespace TruthCore.Epistemology.UltimateExplanation
open TruthCore.Modern.Hume.Induction
open TruthCore.Explanation.HistorySelection
open TruthCore.Modal.HistoryContrastive

/-- A fixed coarse instrument: is at least one of the two candidate members
present? It reports no bearer identity, cause, or grounding information. Both
history alternatives are populated; this projection loses their difference. -/
def occupancy (w : Bool) (n : Nat) : Bool := by
  haveI : Decidable (chains.IsAt w (false,n) n ∨ chains.IsAt w (true,n) n) := by
    change Decidable (false = w ∨ true = w)
    infer_instance
  exact decide (chains.IsAt w (false,n) n ∨ chains.IsAt w (true,n) n)

def globalObservation (signal : Int → Bool × Bool) (n : Nat) : Bool :=
  (signal (Int.ofNat n)).1

/-- Same-history selection can fail while the coarse local observable is exactly
predictable, for both existing source-free and rooted histories. The imported
unique global law also yields the very same observed trace and local predictions.
Global-law truth and availability are conditional; no ultimate adequacy follows. -/
def Integration : Prop :=
  TruthCore.Explanation.HistorySelection.Certificate ∧
  (¬ ∃ p, EvidenceOnly (reasons false).reasonPresent (fun _ => True) p ∧
    Selects chains p false) ∧
  (¬ ∃ p, EvidenceOnly (reasons false).reasonPresent (fun _ => True) p ∧
    Selects rooted p false) ∧
  (∀ w n, Cell stable (occupancy w) n (occupancy w) ∧
    Accurate stable (occupancy w) n ∧ Optimal stable (occupancy w) n .betTrue ∧
    (chains.IsAt w (false,n) n ↔ rooted.IsAt w (false,n) n) ∧
    (chains.IsAt w (true,n) n ↔ rooted.IsAt w (true,n) n)) ∧
  (∀ signal, GlobalLaw signal → ∀ n,
    globalObservation signal n = occupancy false n ∧
    Cell stable (globalObservation signal) n (globalObservation signal) ∧
    Accurate stable (globalObservation signal) n ∧
    Optimal stable (globalObservation signal) n .betTrue)
end TruthCore.Epistemology.UltimateExplanation
