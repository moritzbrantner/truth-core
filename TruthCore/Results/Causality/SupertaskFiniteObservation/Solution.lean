import TruthCore.Causality.Supertasks

namespace TruthCore.Results.Causality.SupertaskFiniteObservation
open TruthCore.Causality

/-- Constant-false and delayed-true traces match every requested finite
prefix while converging under the stipulated stable-output criterion to
opposite terminal values. -/
theorem supertaskFiniteObservation : FiniteObservationCannotFixAllStableOutputs := by
  intro cutoff
  refine ⟨(fun _ => false), (fun n => decide (cutoff < n)), ?_, ?_, ?_⟩
  · intro n hN
    have hNot : ¬ cutoff < n := Nat.not_lt_of_ge hN
    exact decide_eq_false_iff_not.mpr hNot
  · refine ⟨0, ?_⟩
    intro n _
    rfl
  · refine ⟨cutoff + 1, ?_⟩
    intro n hN
    have hLt : cutoff < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self cutoff) hN
    exact decide_eq_true hLt

end TruthCore.Results.Causality.SupertaskFiniteObservation
