import Mathlib.Algebra.Group.Int.Defs

/-! Analyst's additive measurement model, motivated by Duhem's distinction
between a tested hypothesis and its instrumental auxiliaries (La Théorie
physique, II.VI §§I–III). Duhem is not credited with this model or theorem.
The signal function and one constant bias jointly determine every reading;
constant bias, additive response and exact data are explicit model choices. -/
namespace TruthCore.Science.MeasurementCalibration

/-- Exact agreement of all readings in a constant-additive-bias profile. -/
def SameReadings {X V : Type} [Add V] (f g : X → V) (b c : V) : Prop :=
  ∀ x, f x + b = g x + c

/-- A compensating global shift changes the signal and constant bias together.
This relation concerns representation/identifiability, not physical identity. -/
def OffsetShift {X V : Type} [AddGroup V]
    (f g : X → V) (b c d : V) : Prop :=
  c = b - d ∧ ∀ x, g x = f x + d

/-- Exact all-input agreement with an input-dependent bias. This is a separate,
strictly more permissive profile used only for the final omission control. -/
def SameVariableReadings {X V : Type} [Add V]
    (f g b c : X → V) : Prop := ∀ x, f x + b x = g x + c x

/-- Complete additive data determine only a compensating-shift class. A shared
signal value at a supplied input fixes both the constant bias and all signal
values within that class. No epistemic warrant for that anchor is encoded.
Inhabited integer controls witness nonidentification without an anchor and
failure of one-anchor identification when bias may depend on the input. -/
def Certificate : Prop :=
  (∀ (X V : Type) [AddCommGroup V] (f g : X → V) (b c : V),
    SameReadings f g b c ↔ ∃ d, OffsetShift f g b c d) ∧
  (∀ (X V : Type) [AddCommGroup V] (f g : X → V) (b c k : V) (x₀ : X),
    SameReadings f g b c → f x₀ = k → g x₀ = k →
      b = c ∧ ∀ x, f x = g x) ∧
  (∃ (f g : Unit → Int) (b c : Int),
    SameReadings f g b c ∧ (∀ x, f x ≠ g x) ∧ b ≠ c) ∧
  (∃ f g b c : Bool → Int,
    SameVariableReadings f g b c ∧ f false = g false ∧ f true ≠ g true)

end TruthCore.Science.MeasurementCalibration
