import Mathlib.LinearAlgebra.QuadraticForm.Prod
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! A task-local analytic 1+1-dimensional profile in units c=1. The pinned
Mathlib has no Minkowski-space/Lorentz-group definition; we use its quadratic
forms and linear isometry equivalences rather than a bespoke mathematical
isometry. This profile is not an empirical validation of special relativity,
a definition of physical causation, or a definition of metaphysical presence. -/
namespace TruthCore.Spacetime.BoostSimultaneity
noncomputable section

abbrev Event := ℝ × ℝ

/-- The Lorentzian quadratic interval, not a positive-definite norm. -/
def interval : QuadraticForm ℝ Event :=
  (QuadraticMap.sq : QuadraticForm ℝ ℝ).prod
    (-(QuadraticMap.sq : QuadraticForm ℝ ℝ))

@[simp] theorem interval_apply (p : Event) : interval p = p.1 * p.1 - p.2 * p.2 := by
  simp [interval, QuadraticMap.prod, QuadraticMap.sq, QuadraticMap.linMulLin, sub_eq_add_neg]

/-- Rational boost with v=4/5 and gamma=5/3; no approximation to a square root. -/
def boostLinear : Event ≃ₗ[ℝ] Event where
  toFun p := ((5 * p.1 - 4 * p.2) / 3, (5 * p.2 - 4 * p.1) / 3)
  invFun p := ((5 * p.1 + 4 * p.2) / 3, (5 * p.2 + 4 * p.1) / 3)
  left_inv p := by ext <;> dsimp <;> ring
  right_inv p := by ext <;> dsimp <;> ring
  map_add' p q := by ext <;> dsimp <;> ring
  map_smul' r p := by ext <;> dsimp <;> ring

/-- Isometry of the actual Mathlib quadratic form; lightlike nonzero vectors
have interval zero, so this is not a metric isometry of Euclidean distance. -/
def boost : interval.IsometryEquiv interval where
  toLinearEquiv := boostLinear
  map_app' p := by simp [boostLinear]; ring

/-- Future-directed nonspacelike displacement, including the zero vector.
This geometric relation is not an assertion that any physical cause operates. -/
def FutureCone (p : Event) : Prop := |p.2| ≤ p.1

/-- Frame simultaneity means equality of that frame's coordinate times. -/
def Simultaneous (p q : Event) : Prop := p.1 = q.1

/-- Future-cone order of event differences, not ordinary efficient causation. -/
def GeometricBefore (p q : Event) : Prop := FutureCone (q - p)

def origin : Event := (0, 0)
def separated : Event := (0, 1)

/-- Exact two-frame interval/cone control and a populated spacelike witness.
No relation can equal both frames' simultaneity relations. A selected preferred
relation may equal one frame only; no absence of a privileged present follows.
Worlds/histories, tensed A-properties and actual causal edges are not identified
with events, real coordinates or GeometricBefore. -/
def Controls : Prop :=
  (∀ p, interval (boost p) = interval p) ∧
  (∀ p, FutureCone (boost p) ↔ FutureCone p) ∧
  (∀ p q, GeometricBefore (boost p) (boost q) ↔ GeometricBefore p q) ∧
  (origin ≠ separated ∧ interval (separated - origin) = -1 ∧
    Simultaneous origin separated ∧ ¬ Simultaneous (boost origin) (boost separated)) ∧
  (¬ ∃ P : Event → Event → Prop,
    (∀ p q, P p q ↔ Simultaneous p q) ∧
    (∀ p q, P p q ↔ Simultaneous (boost p) (boost q))) ∧
  (∃ P : Event → Event → Prop,
    (∀ p q, P p q ↔ Simultaneous p q) ∧
    ¬ (∀ p q, P p q ↔ Simultaneous (boost p) (boost q)))

end
end TruthCore.Spacetime.BoostSimultaneity
