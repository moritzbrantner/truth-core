import Mathlib.Analysis.SpecialFunctions.Exp
import TruthCore.Causality.BoundedPastResource
import TruthCore.Results.Causality.BoundedPastResource.Solution

/-! Two omission controls for the uniform-growth resource constraint.
The whole integer grid, ordered in its usual direction, supplies a beginningless
past ending at zero: every t ≤ 0 has an earlier integer t - 1. The real-valued
stock is a mathematical assignment, not entropy, a clock budget, or a proof of
physical or metaphysical realization. No assumption about becoming is encoded.
-/
namespace TruthCore.Models.PastResourceControls
open TruthCore.Causality.BoundedPastResource

/-- A strictly increasing positive stock on the full integer grid. -/
noncomputable def expStock (t : Int) : ℝ := Real.exp (t : ℝ)

/-- A stock with exactly one unit of growth at each integer step. -/
def linearStock (t : Int) : ℝ := (t : ℝ)

/-- Lower boundedness and strict growth need not yield a uniform positive
increment. Conversely, uniform positive growth alone does not yield a lower
bound over the whole past. These are joint assignments on the same Int grid,
not a splice of separate worlds or a claim that every stock is realizable. -/
def JointControls : Prop :=
  (PastLowerBound expStock 0 0 ∧
    (∀ t : Int, t < 0 → expStock t < expStock (t + 1)) ∧
    ¬ ∃ ε : ℝ, PositiveStep ε ∧ UniformPastGrowth expStock 0 ε) ∧
  (PositiveStep 1 ∧ UniformPastGrowth linearStock 0 1 ∧
    ¬ ∃ L : ℝ, PastLowerBound linearStock 0 L)

end TruthCore.Models.PastResourceControls
