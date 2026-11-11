module

public import TruthCore.Epistemology.SleepingBeauty1401.Reflection
public import TruthCore.Results.Logic.EpistemicAccuracy.Solution
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

@[expose] public section
namespace TruthCore.Results.Epistemology.SleepingBeauty1401.Reflection
open TruthCore.Epistemology.SleepingBeauty1401
open TruthCore.Epistemology.SleepingBeauty1401.Reflection

theorem amnesiaControl : AmnesiaControl := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [beforeCredence, coinPosterior, revealed]
  · norm_num [beforeCredence, coinPosterior, revealed]
  · intro w
    norm_num [afterCredence, coinPosterior, erased]
  · intro w
    cases w <;> norm_num [coinPosterior, revealed, afterCredence, erased, beforeCredence]
  · norm_num [coinPosterior]
  · rintro ⟨f, hf⟩
    have hh := hf .heads
    have ht := hf .tails
    have : World.heads = .tails := hh.symm.trans ht
    cases this
  · exact ⟨fun _ => (), by intro w; rfl⟩

theorem irrelevantLossControl : IrrelevantLossControl := by
  refine ⟨?_, ?_, ?_⟩
  · intro b
    cases b <;> norm_num [pairPosterior]
  · norm_num [pairPosterior]
  · rintro ⟨f, hf⟩
    have hh := hf (.heads, true)
    have ht := hf (.heads, false)
    have : true = false := hh.symm.trans ht
    cases this

theorem firstMondayCalibration : FirstMondayCalibration := by
  refine ⟨?_, ?_, ?_⟩
  · intro r
    norm_num [coinPosterior]
  · norm_num [coinPosterior]
  · exact ⟨id, by intro w; rfl⟩

theorem cohortAccuracy : CohortAccuracy := by
  have hm : ∀ r : ℝ, mondayRisk r - mondayRisk (1/2) = (r-1/2)^2 := by
    intro r
    exact TruthCore.Results.Logic.EpistemicAccuracy.regret (1/2) r
  have ht : ∀ r : ℝ, tokenRisk r - tokenRisk (1/3) = (3/2)*(r-1/3)^2 := by
    intro r
    dsimp [tokenRisk]
    ring
  have mm : ∀ r : ℝ, (∀ s, mondayRisk r ≤ mondayRisk s) ↔ r=1/2 := by
    intro r
    constructor
    · intro h
      have := h (1/2)
      have := hm r
      nlinarith [sq_nonneg (r-1/2)]
    · rintro rfl s
      have := hm s
      nlinarith [sq_nonneg (s-1/2)]
  have mt : ∀ r : ℝ, (∀ s, tokenRisk r ≤ tokenRisk s) ↔ r=1/3 := by
    intro r
    constructor
    · intro h
      have := h (1/3)
      have := ht r
      nlinarith [sq_nonneg (r-1/3)]
    · rintro rfl s
      have := ht s
      nlinarith [sq_nonneg (s-1/3)]
  refine ⟨hm, ht, mm, mt, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨r, h, t⟩
    have := (mm r).mp h
    have := (mt r).mp t
    linarith
  · norm_num [mondayRisk, TruthCore.Logic.EpistemicAccuracy.error]
  · norm_num [tokenRisk]
  · norm_num
  · norm_num

theorem recallControl : RecallControl := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro mon tue
    dsimp [dayRisk]
    ring
  · norm_num [dayRisk]
  · norm_num [tokenRisk]
  · intro r
    dsimp [dayRisk, tokenRisk]
    ring
  · norm_num [dayRisk, tokenRisk]

end TruthCore.Results.Epistemology.SleepingBeauty1401.Reflection
