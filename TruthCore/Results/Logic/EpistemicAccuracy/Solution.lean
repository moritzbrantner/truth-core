module

public import TruthCore.Logic.EpistemicAccuracy

@[expose] public section
namespace TruthCore.Results.Logic.EpistemicAccuracy
open TruthCore.Logic.EpistemicAccuracy

theorem regret (q r : ℝ) : error q r - error q q = (r-q)^2 := by
  unfold error
  ring

/-- This establishes the cost comparison; it contains no ought/reason premise. -/
theorem certificate : Certificate := by
  refine ⟨regret, ?_, ?_, ?_, ?_⟩
  · intro q r
    have := regret q r
    nlinarith [sq_nonneg (r-q)]
  · intro q r
    constructor
    · intro h
      have := regret q r
      nlinarith [sq_nonneg (r-q)]
    · intro h
      subst r
      rfl
  · intro q c r ε hε hq hfar
    rcases hq with ⟨hlo, hhi⟩
    have hid : error q r - error q c = (r-c)*(r+c-2*q) := by
      unfold error
      ring
    rcases hfar with hright | hleft
    · have ha : 0 < r-c := by linarith
      have hb : 0 < r+c-2*q := by linarith
      have := mul_pos ha hb
      linarith
    · have ha : r-c < 0 := by linarith
      have hb : r+c-2*q < 0 := by linarith
      have := mul_pos_of_neg_of_neg ha hb
      linarith
  · norm_num [error]
end TruthCore.Results.Logic.EpistemicAccuracy
