import TruthCore.Modal.SelectedEffectBridge

/-! Stipulative finite decision table, motivated by the free-will definition
fork in Carneades's public article and video KODJicKd5ps. No sourced claim:
complete input means the explicitly selected input of this table, not a proved
complete physical state. Constraint absence is not identified with freedom or
responsibility. See docs/notes/carneades-choice-context.md. -/
namespace TruthCore.Modal.ChoiceContext
open TruthCore.Modal.SelectedEffectBridge

/-- Histories separately record a response-law selector, prior preference,
and an imposed constraint that forces the `true` action. -/
structure History where
  law : Bool
  preference : Bool
  imposed : Bool
  deriving DecidableEq

/-- The complete input of this stipulated table includes the imposed constraint. -/
def input (h : History) : Bool × Bool := (h.preference, h.imposed)

/-- A constraint overrides preference; otherwise law `false` follows preference
and law `true` reverses it. This is a table, not a theory of coercion. -/
def response (law : Bool) (c : Bool × Bool) : Bool :=
  if c.2 then true else if law then !c.1 else c.1

def action (h : History) : Bool := response h.law (input h)

/-- Same law AND same complete table input, without fixing the output by fiat. -/
def SameContext (h k : History) : Prop := h.law = k.law ∧ input h = input k

/-- Different output while retaining the stipulated law and complete input. -/
def Alternative (h : History) : Prop :=
  ∃ k, SameContext h k ∧ action h ≠ action k

/-- The constraint is absent; no sufficiency claim about free will or desert. -/
def Unconstrained (h : History) : Prop := h.imposed = false

def actual : History := ⟨false, true, false⟩
def changedInput : History := ⟨false, false, false⟩
def changedLaw : History := ⟨true, true, false⟩
def constrained : History := ⟨false, false, true⟩

/-- One fixed relational law: imposed constraints require `true`; absent a
constraint both actions are lawful. Nondeterminism here is nonfunctionality
of this same relation, not violation of it or a physical possibility claim. -/
def relationalLaw (c : Bool × Bool) (a : Bool) : Prop :=
  c.2 = true → a = true

/-- Conditional transfer reuses the existing output semantics; neither law nor
complete input may vary at accessible worlds. The finite table distinguishes
law variation, input variation, and constraint status from actual action. -/
def Controls : Prop :=
  (∀ (W B A L C : Type) (p : OutputProfile W B A) (w : W) (a : A)
      (law : W → L) (condition : W → C) (r : L × C → B),
    (∀ v, p.ontic.frame.access w v → law v = law w ∧ condition v = condition w) →
    (∀ v x, p.output v a x ↔ x = r (law v, condition v)) →
    StableActOutput p w a) ∧
  (∀ h, ¬ Alternative h) ∧
  (Unconstrained actual ∧ action actual = true) ∧
  (actual.law = changedInput.law ∧ input actual ≠ input changedInput ∧
    action actual ≠ action changedInput) ∧
  (input actual = input changedLaw ∧ actual.law ≠ changedLaw.law ∧
    action actual ≠ action changedLaw) ∧
  (¬ Unconstrained constrained ∧ action constrained = action actual) ∧
  (relationalLaw (input actual) false ∧ relationalLaw (input actual) true ∧
    false ≠ true) ∧
  (∀ c a, c.2 = true → relationalLaw c a → a = true)
end TruthCore.Modal.ChoiceContext
