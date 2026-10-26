import TruthCore.Causality.ConvergentSchedule

namespace TruthCore.Results.Causality.ConvergentZenoSchedule
open TruthCore.Causality
open Filter Topology

/-- The stage times `1 - (1/2)^n` form a strictly increasing real schedule
below `1` that converges to the endpoint time `1`, the stage durations
`(1/2)^(n+1)` telescope and sum to `1`, and the clock embeds the supertask
order `SupertaskPrecedes` into `<` on the reals. A mathematical model only; no
physical execution is asserted. -/
theorem convergentZenoSchedule : ConvergentZenoSchedule := by
  have hHalfPos : (0 : ℝ) < 1 / 2 := by norm_num
  have hHalfLt : (1 / 2 : ℝ) < 1 := by norm_num
  -- Strict monotonicity: `(1/2)^n` is strictly antitone.
  have hMono : StrictMono zenoStageTime := by
    intro m n hmn
    unfold zenoStageTime
    have := pow_lt_pow_right_of_lt_one₀ hHalfPos hHalfLt hmn
    linarith
  -- Every stage time is below the endpoint.
  have hBelow : ∀ n, zenoStageTime n < 1 := by
    intro n
    unfold zenoStageTime
    have := pow_pos hHalfPos n
    linarith
  refine ⟨hMono, hBelow, ?_, ?_, ?_, ?_⟩
  · -- `(1/2)^n → 0`, so `1 - (1/2)^n → 1`.
    have hPow : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hHalfPos.le hHalfLt
    have hSub := (tendsto_const_nhds (x := (1 : ℝ))).sub hPow
    simpa [zenoMomentTime, zenoStageTime] using hSub
  · intro n
    unfold zenoStageTime zenoStageDuration
    ring
  · -- `∑ (1/2)^(n+1) = (1/2) * ∑ (1/2)^n = (1/2) * 2 = 1`.
    have h := hasSum_geometric_two.mul_left (1 / 2 : ℝ)
    have hEq : (fun n : ℕ => (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ n) = zenoStageDuration := by
      funext n
      unfold zenoStageDuration
      ring
    rw [hEq] at h
    norm_num at h
    exact h
  · intro a b
    cases a with
    | stage m =>
      cases b with
      | stage n => exact hMono.lt_iff_lt.symm
      | limit => exact ⟨fun _ => hBelow m, fun _ => trivial⟩
    | limit =>
      cases b with
      | stage n =>
        refine ⟨fun h => h.elim, fun h => ?_⟩
        exact absurd h (not_lt.mpr (hBelow n).le)
      | limit =>
        refine ⟨fun h => h.elim, fun h => ?_⟩
        exact absurd h (lt_irrefl _)

end TruthCore.Results.Causality.ConvergentZenoSchedule
