import TruthCore.Causality.ConvergentSchedule
import TruthCore.Causality.RegressReadings
import Mathlib.Data.Int.Order.Basic
import Mathlib.Tactic

/-! Analyst-defined mathematical controls, with no physical realizability claim.
The existing convergent schedule has a first stage. Reflecting its clock gives
an event population with no least event in a time interval that has a first
instant. Event indices are labels, not chronological order.

Implication-failure matrix (all within the stipulated mathematics):
* Bounded elapsed duration does not force a least event: reflected Zeno clock.
* A first instant does not force a first event: the same closed interval.
* Unbounded temporal past does not force causal regress: integer time with no
  causal edges.
The no-first-*time* bounded-age interval (0,1] is the distinct control of PR609;
it is not reconstructed here. None of these controls proves physical possibility. -/
namespace TruthCore.Causality.TemporalEventControls

/-- Closed real interval with its usual Mathlib subtype order. -/
abbrev BoundedTime := Set.Icc (0 : ℝ) 1

/-- Reverse the existing Zeno clock; event zero occurs at one, not at zero. -/
noncomputable def eventTime (n : ℕ) : ℝ := 1 - zenoStageTime n

/-- Empty causation on the integer event/time carrier. Temporal order remains
usual integer order and is not used as a causal relation. -/
def independentCauses (_ _ : ℤ) : Prop := False

/-- A bounded carrier with first instant zero and a positive event schedule
with an earlier event for every event; and unbounded integer past with empty,
well-founded causation and no infinite descending causal series. These closed
controls refute the corresponding universal implications only in this stated
mathematical semantics. -/
def Controls : Prop :=
  (∃ first : BoundedTime, (first : ℝ) = 0 ∧ ∀ t : BoundedTime, first ≤ t) ∧
  (∀ n, 0 < eventTime n ∧ eventTime n ≤ 1) ∧
  (∀ n, ∃ m, eventTime m < eventTime n) ∧
  (∀ bound : ℤ, ∃ t : ℤ, t < bound) ∧
  (∀ x y, ¬ independentCauses x y) ∧
  WellFounded independentCauses ∧
  NoInfiniteDescendingPerSeSeries independentCauses

end TruthCore.Causality.TemporalEventControls
