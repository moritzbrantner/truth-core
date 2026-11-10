module

public import TruthCore.Causality.ContractiveBorrowedPower

@[expose] public section
open scoped BoundedContinuousFunction NNReal
namespace TruthCore.Results.Causality.ContractiveBorrowedPower
open TruthCore.Causality.ContractiveBorrowedPower

theorem zeroExercise : ZeroExercise := by
  intro V _ T q P hT hzero hP _
  exact hT.fixedPoint_unique' hP hzero

theorem controls : Controls := by
  refine ⟨by norm_num, ?_, ⟨?_, ?_⟩, ⟨by norm_num, by norm_num⟩, ?_⟩
  · intro n
    dsimp
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h2 : (0 : ℝ) < (n : ℝ)+2 := by positivity
    have h3 : (0 : ℝ) < (n : ℝ)+3 := by positivity
    refine ⟨by positivity, (div_le_one h2).2 (by linarith), ?_, ?_, ?_⟩
    · have : 1 / ((n : ℝ)+2)^2 < 1 := (div_lt_one (sq_pos_of_pos h2)).2 (by nlinarith)
      linarith
    · have : 0 < 1 / ((n : ℝ)+2)^2 := by positivity
      linarith
    · field_simp
      ring
  · intro n
    rw [pow_succ]
    ring
  · intro M
    simpa only [show (1 : ℝ) + 1 = 2 by norm_num] using add_one_pow_unbounded_of_pos M (by norm_num : (0 : ℝ) < 1)
  · refine ⟨fun _ => 0, 0, ⟨by norm_num, ?_⟩, rfl, rfl⟩
    exact LipschitzWith.of_dist_le_mul (by simp)

end TruthCore.Results.Causality.ContractiveBorrowedPower
