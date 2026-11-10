module
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic


/-! Analyst energy ledger for a flywheel driving a dissipative load over one
fixed interval. No empirical law or metaphysical applicability is asserted. -/
@[expose] public section
namespace TruthCore.Causality.ProductiveStore
open scoped BigOperators

/-- All fields are energies in one common unit over one fixed interval.
`before` and `after` count the SAME identified flywheel's kinetic-energy store;
`input` crosses the chosen subsystem boundary; `work` leaves through the selected
load port; `heat` is the remaining exported dissipation. Internal transport is
not counted again as input. Nonnegativity and balance are hypotheses, not the
meaning of production, sourcehood, or causation. -/
structure Ledger where
  before : ℝ
  after : ℝ
  input : ℝ
  work : ℝ
  heat : ℝ

def Admissible (m : Ledger) : Prop :=
  0 ≤ m.before ∧ 0 ≤ m.after ∧ 0 ≤ m.input ∧ 0 ≤ m.work ∧ 0 ≤ m.heat ∧
  m.after + m.work + m.heat = m.before + m.input

/-- Nondepletion is stronger than finite initial stock. Closure is only closure
of this energy port, not absence of existential support or enabling conditions. -/
def Budget : Prop := ∀ m : Ledger, Admissible m →
  m.work + m.heat ≤ m.before + m.input ∧
  (m.before ≤ m.after → 0 < m.work + m.heat → 0 < m.input)

/-- Concrete omission and nonvacuity controls, all in the same energy meaning:
closed transient discharge, closed steady maintenance, replenished steady work.
The heat-only case tests that work output and dissipation are different fields. -/
def Controls : Prop :=
  Admissible ⟨2, 0, 0, 1, 1⟩ ∧
  Admissible ⟨2, 2, 0, 0, 0⟩ ∧
  Admissible ⟨2, 2, 2, 1, 1⟩ ∧
  Admissible ⟨2, 0, 0, 0, 2⟩ ∧
  ¬Admissible ⟨2, 2, 0, 1, 1⟩

/-- A sequence of aggregate ledgers: the store at t+1 is the same stock used
as the after-stock at t. Every finite total output is bounded by initial stock
plus accumulated external input. No stationarity or uniform contraction. -/
def TemporalBudget : Prop := ∀ (stock input output : ℕ → ℝ),
  (∀ t, 0 ≤ stock t) →
  (∀ t, stock (t+1) + output t = stock t + input t) →
  ∀ n, (∑ t ∈ Finset.range n, output t) ≤
    stock 0 + ∑ t ∈ Finset.range n, input t
/-- Closed discharge at every natural interval, with decreasing positive work
and heat; finite initial stock does not prohibit infinitely many positive outputs.
This is an interval ledger model, not a derived solution of rotational dynamics. -/
def DecayingDischarge : Prop := ∀ n : ℕ,
  let e : ℝ := (1/2)^n
  Admissible ⟨2*e, 2*((1/2)^(n+1)), 0, e/2, e/2⟩ ∧ 0 < e/2
end TruthCore.Causality.ProductiveStore
