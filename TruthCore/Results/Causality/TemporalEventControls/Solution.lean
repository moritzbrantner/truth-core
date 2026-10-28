import TruthCore.Causality.TemporalEventControls
namespace TruthCore.Results.Causality.TemporalEventControls
open TruthCore.Causality TruthCore.Causality.TemporalEventControls
/-- First time, first event, metric boundedness and causal regress are distinct. -/
theorem controls : TruthCore.Causality.TemporalEventControls.Controls := by
  have htime (n : ℕ) : eventTime n = (1 / 2 : ℝ) ^ n := by
    simp [eventTime, zenoStageTime]
  have hpos (n : ℕ) : 0 < eventTime n := by
    rw [htime]; positivity
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨⟨0, by norm_num⟩, rfl, fun t => t.property.1⟩
  · intro n
    exact ⟨hpos n, by rw [htime]; exact pow_le_one₀ (by norm_num) (by norm_num)⟩
  · intro n
    refine ⟨n + 1, ?_⟩
    rw [htime, htime, pow_succ]
    have hp := hpos n
    rw [htime] at hp
    linarith
  · intro bound
    exact ⟨bound - 1, by omega⟩
  · intro x y h
    exact h
  · exact ⟨fun x => Acc.intro x (fun _ h => False.elim h)⟩
  · rintro ⟨series, h⟩
    exact h 0
end TruthCore.Results.Causality.TemporalEventControls
