import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Function.Conjugate

/-!
An analyst's #326 intervention model, not an attribution to a historical author.
Individual bearers are two primitive components. Microstates, macrostates and
commands are mathematical descriptions, not additional individual bearers.
Identity-only parthood is an explicit nihilist profile, not a claim about nature.
The exact intervention family matters: joint writes and swaps admit a closed
AND-response dynamics; adding a local bit flip destroys that coarse closure.
This establishes reproduction of the specified response histories, not a
reduction of all causal powers, intentional agency or explanatory sufficiency.
-/
namespace TruthCore.Mereology.ArrangementDynamics

/-- Every intervention preserves equality of the selected coarse data.
Uses Mathlib's existing fiber-constancy notion, rather than a second one. -/
def Preserves {S M I : Type} (observe : S → M) (step : I → S → S) : Prop :=
  ∀ i, Function.FactorsThrough (observe ∘ step i) observe

/-- Each primitive intervention semiconjugates to the proposed macro transition. -/
def Realizes {S M I : Type} (observe : S → M) (step : I → S → S)
    (macroStep : I → M → M) : Prop :=
  ∀ i, Function.Semiconj observe (step i) (macroStep i)

/-- Ordered finite intervention histories; the first command acts first. -/
def run {S I : Type} (step : I → S → S) (s : S) : List I → S
  | [] => s
  | i :: rest => run step (step i s) rest

inductive Intervention where
  | write (left right : Bool)
  | swap
  deriving DecidableEq

abbrev Micro := Bool × Bool

/-- One component's bit per coordinate; no third material bearer is introduced. -/
def primitiveStep : Intervention → Micro → Micro
  | .write a b, _ => (a, b)
  | .swap, s => (s.2, s.1)

/-- `coupled` is a stipulated arrangement parameter. -/
def observe (coupled : Bool) (s : Micro) : Bool :=
  coupled && (s.1 && s.2)

def macroStep (coupled : Bool) : Intervention → Bool → Bool
  | .write a b, _ => coupled && (a && b)
  | .swap, output => output

/-- An additional local intervention not included in `Intervention`. -/
def flipLeft (s : Micro) : Micro := (!s.1, s.2)

/-- Material parthood in this explicitly chosen nihilist profile. -/
def Part (a b : Bool) : Prop := a = b

def ProperPart (a b : Bool) : Prop := Part a b ∧ a ≠ b

/-- Exact general reduction criterion, finite-history preservation, and the
inhabited two-simple nonlinear response/control family. No empirical premise,
metaphysical possibility or adequate-explanation claim is encoded. -/
def Certificate : Prop :=
  (∀ (S M I : Type) (o : S → M) (f : I → S → S),
    (∃ g : I → M → M, Realizes o f g) ↔ Preserves o f) ∧
  (∀ (S M I : Type) (o : S → M) (f : I → S → S) (g : I → M → M),
    Realizes o f g → ∀ s word, o (run f s word) = run g (o s) word) ∧
  (∀ coupled, Realizes (observe coupled) primitiveStep (macroStep coupled)) ∧
  (¬ ∃ a b : Bool, ProperPart a b) ∧
  (observe true (false, false) = false ∧
    observe true (true, false) = false ∧
    observe true (false, true) = false ∧
    observe true (true, true) = true) ∧
  (observe false (true, true) = false ∧ observe true (true, true) = true) ∧
  (¬ ∃ g : Bool → Bool, ∀ s,
    observe true (flipLeft s) = g (observe true s))

end TruthCore.Mereology.ArrangementDynamics
