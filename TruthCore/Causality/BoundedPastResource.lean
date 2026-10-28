import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Int.Order.Basic
import TruthCore.Logic.Configuration

/-! A neutral real-valued stock on integer time, not an empirical entropy law.
The past is the entire integer half-line at or before now. Real values are
Archimedean; every indexed step has the same unit duration. A lower stock bound
and uniform positive stock growth are explicit, independently open hypotheses.
No finite duration since a first event, causal well-foundedness or event-count
bound is assumed. The Causality namespace does not identify stock with a cause.
-/
namespace TruthCore.Causality.BoundedPastResource

/-- One fixed positive real increment, not a separate positive amount per step. -/
def PositiveStep (ε : ℝ) : Prop := 0 < ε

/-- One real lower bound works throughout the integer past, including now. -/
def PastLowerBound (S : Int → ℝ) (now : Int) (L : ℝ) : Prop :=
  ∀ t, t ≤ now → L ≤ S t

/-- Every unit step wholly in the past adds at least the same epsilon.
This is stronger than strict growth or a merely positive varying increment. -/
def UniformPastGrowth (S : Int → ℝ) (now : Int) (ε : ℝ) : Prop :=
  ∀ t, t < now → S t + ε ≤ S (t + 1)

end TruthCore.Causality.BoundedPastResource
