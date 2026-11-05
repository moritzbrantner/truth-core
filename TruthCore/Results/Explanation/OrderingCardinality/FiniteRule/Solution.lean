module

public import TruthCore.Explanation.OrderingCardinality

@[expose] public section

namespace TruthCore.Results.Explanation.OrderingCardinality.FiniteRule
open TruthCore.Explanation.OrderingCardinality

/-- A finite inductive term verifies all values of the closed recursive program;
there is no hypothesis already asserting its infinitely many test outcomes. -/
theorem verifies : FiniteRule := by
  intro n
  constructor
  · induction n with
    | zero => rfl
    | succ n ih => exact congrArg Nat.succ ih
  · rfl

end TruthCore.Results.Explanation.OrderingCardinality.FiniteRule
