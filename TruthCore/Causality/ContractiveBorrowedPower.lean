module

public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Tactic

/-! Quantitative analyst reconstruction for #1378. V is one fixed exercise
context. No identification with existential grounding or inductive Supply.
For discrete V every bounded assignment is continuous. Nonnegativity restricts
productive assignments; the ambient real normed space also contains signed ones.
See docs/notes/contractive-borrowed-power-1378.md for OPEN applicability bridges. -/
@[expose] public section
open scoped BoundedContinuousFunction NNReal
namespace TruthCore.Causality.ContractiveBorrowedPower

/-- Uniqueness against the zero fixed point, specialized to bounded assignments.
No completeness, linearity, positivity of T or well-founded graph is required. -/
def ZeroExercise : Prop :=
  ∀ (V : Type) [TopologicalSpace V] (T : (V →ᵇ ℝ) → (V →ᵇ ℝ))
    (q : ℝ≥0) (P : V →ᵇ ℝ),
    ContractingWith q T → T 0 = 0 → T P = P →
    (∀ v, 0 ≤ P v) → P = 0

/-- Controls test mathematical assumptions, not metaphysical possibility.
Binary branching has row sum one. Nonuniform loss uses bounded P_n with
strict factors below one. The uniform-loss chain has unbounded powers.
The affine scalar transfer has hidden intrinsic input. -/
def Controls : Prop :=
  ((1 : ℝ) = (1/2)*1 + (1/2)*1) ∧
  (∀ n : ℕ,
    let p := ((n : ℝ)+1)/((n : ℝ)+2)
    let next := ((n : ℝ)+2)/((n : ℝ)+3)
    let q := 1 - 1/((n : ℝ)+2)^2
    0 < p ∧ p ≤ 1 ∧ 0 < q ∧ q < 1 ∧ p = q*next) ∧
  ((∀ n : ℕ, (2 : ℝ)^n = (1/2)*2^(n+1)) ∧
    (∀ M : ℝ, ∃ n : ℕ, M < (2 : ℝ)^n)) ∧
  ((1 : ℝ) = 1/2 + (1/2)*1 ∧ (0 : ℝ) ≠ 1/2 + (1/2)*0) ∧
  (∃ (T : ℝ → ℝ) (q : ℝ≥0), ContractingWith q T ∧ T 0 = 0 ∧ T 0 = 0)
end TruthCore.Causality.ContractiveBorrowedPower
