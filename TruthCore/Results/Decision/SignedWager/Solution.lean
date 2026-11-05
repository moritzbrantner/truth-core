module

public import TruthCore.Decision.SignedWager

@[expose] public section

namespace TruthCore.Results.Decision.SignedWager
open TruthCore.Decision.SignedWager

private theorem rewarded (s c : ℝ) (hs : 0 < s) :
    expectation s ⊤ c = some ⊤ := by
  rw [expectation, EReal.coe_mul_top_of_pos hs, ← EReal.coe_mul]
  simp only [add, EReal.coe_ne_bot, top_ne_bot, and_false, false_and, or_self, ite_false,
    EReal.top_add_coe]

private theorem successProbability (p q : ℝ) (hp : Probability p)
    (hq : Probability q) : Probability (p * q + (1 - p) * (1 - q)) := by
  constructor
  · exact add_nonneg (mul_nonneg hp.1 hq.1)
      (mul_nonneg (sub_nonneg.mpr hp.2) (sub_nonneg.mpr hq.2))
  · have h₁ := mul_nonneg hp.1 (sub_nonneg.mpr hq.2)
    have h₂ := mul_nonneg (sub_nonneg.mpr hp.2) hq.1
    nlinarith

private theorem successPositive (p q : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hq : Probability q) : 0 < p * q + (1 - p) * (1 - q) := by
  by_cases h : q = 0
  · subst q; nlinarith
  · have hq' : 0 < q := lt_of_le_of_ne hq.1 (Ne.symm h)
    have ha := mul_pos hp hq'
    have hb := mul_nonneg (sub_nonneg.mpr hp'.le) (sub_nonneg.mpr hq.2)
    linarith

theorem signedConsequences : SignedConsequences := by
  refine ⟨TruthCore.Results.Decision.InfiniteWager.mixtureTie, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p q c _ _ hp hq
    exact rewarded (p*q) c (mul_pos hp hq)
  · intro p q hp hq
    exact successProbability p q hp hq
  · intro p q c hp hp' hq
    exact rewarded _ c (successPositive p q hp hp' hq)
  · intro c
    simp [single, expectation, add]
  · intro p hp hp'
    rw [expectation, EReal.coe_mul_top_of_pos hp,
      EReal.coe_mul_bot_of_pos (by linarith : 0 < 1-p)]
    simp [add]
  · intro c
    simp [expectation, add]
  · intro c
    exact rewarded 1 c (by norm_num)

theorem practicalNontruth : PracticalNontruth := by
  refine ⟨(fun w => w = true), false, 1/2, 1, -1, by decide, rfl,
    ⟨by norm_num, by norm_num⟩, by norm_num, by norm_num, by norm_num, ?_, ?_, ?_,
    by norm_num, ?_, ?_⟩
  · refine ⟨⟨by norm_num, by norm_num⟩, ⊤, ?_, ?_⟩
    · exact rewarded _ _ (by norm_num)
    · intro r w _ _; exact le_top
  · intro r hr
    refine ⟨hr, ⊤, ?_, ?_⟩
    · exact rewarded _ _ (successPositive _ _ (by norm_num) (by norm_num) hr)
    · intro s w _ _; exact le_top
  · change expectation _ ⊤ _ = expectation _ ⊤ _
    rw [rewarded _ _ (by norm_num), rewarded _ _ (by norm_num)]
  · have hf : (1 : EReal) ≠ ⊥ := EReal.coe_ne_bot 1
    simp [single, expectation, add, hf]
  · have hf : (1 : EReal) ≠ ⊥ := EReal.coe_ne_bot 1
    simp [single, expectation, add, hf]

end TruthCore.Results.Decision.SignedWager
