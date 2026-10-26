import TruthCore.Causality.Supertasks

namespace TruthCore.Results.Causality.SupertaskUnitCostDiverges
open TruthCore.Causality

private theorem unitCostPartialSum_eq (n : Nat) : UnitCostPartialSum n = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change UnitCostPartialSum n + 1 = n + 1
    exact congrArg (fun k : Nat => k + 1) ih

/-- Every proposed budget is exceeded by taking one more unit-cost stage. -/
theorem supertaskUnitCostDiverges : UnitCostSeriesUnbounded := by
  intro budget
  refine ⟨budget + 1, ?_⟩
  rw [unitCostPartialSum_eq]
  exact Nat.lt_succ_self budget

end TruthCore.Results.Causality.SupertaskUnitCostDiverges
