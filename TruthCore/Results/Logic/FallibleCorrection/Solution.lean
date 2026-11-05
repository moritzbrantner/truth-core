module

public import TruthCore.Logic.FallibleCorrection
public import TruthCore.Results.Logic.CorrectionCriterion.Solution
public import TruthCore.Results.Logic.EpistemicAccuracy.Solution
public import TruthCore.Results.Logic.EpistemicAccuracy.Statewise.Solution
public import TruthCore.Results.Logic.TranscendentalPractice.InquiryAccess.Solution

@[expose] public section
namespace TruthCore.Results.Logic.FallibleCorrection
open TruthCore.Logic.FallibleCorrection

private theorem partition {N : ℕ} (w : Fin N → ℚ) (a : Fin N → Bool) :
    mass w a false + mass w a true = ∑ i, w i := by
  rw [mass, mass, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases a i <;> simp

private theorem update_total {N : ℕ} (w : Fin N → ℚ)
    (a : Fin N → Bool) (b : Bool) :
    (∑ i, update w a b i) = mass w a b + mass w a (!b) / 2 := by
  simp only [mass, Finset.sum_div, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases h : a i <;> cases b <;> simp [update, h]

private theorem step {N : ℕ} (w : Fin N → ℚ)
    (a : Fin N → Bool) (b : Bool) (hw : ∀ i, 0 ≤ w i) :
    (∑ i, update w a b i) ≤
      (∑ i, w i) * (if predict w a = b then 1 else 3/4) := by
  have h0 : 0 ≤ mass w a false := Finset.sum_nonneg (fun i _ => by
    split <;> simp_all)
  have h1 : 0 ≤ mass w a true := Finset.sum_nonneg (fun i _ => by
    split <;> simp_all)
  have hp := partition w a
  rw [update_total]
  cases b <;> by_cases h : mass w a false ≤ mass w a true <;>
    simp [predict, h] <;> linarith

private theorem positive {N : ℕ} (a : ℕ → Fin N → Bool)
    (f : ℕ → Bool) (n : ℕ) (i : Fin N) : 0 < weights a f n i := by
  induction n with
  | zero => simp [weights]
  | succ n ih =>
    simp only [weights, update]
    split
    · exact ih
    · exact div_pos ih (by norm_num)

private theorem expert_weight {N : ℕ} (a : ℕ → Fin N → Bool)
    (f : ℕ → Bool) (n : ℕ) (i : Fin N) :
    weights a f n i = (1/2 : ℚ) ^ mistakes (fun t => a t i) f n := by
  induction n with
  | zero => simp [weights, mistakes]
  | succ n ih =>
    simp only [weights, update, mistakes]
    split <;> simp_all [pow_succ, div_eq_mul_inv]

private theorem potential {N : ℕ} (a : ℕ → Fin N → Bool)
    (f : ℕ → Bool) (n : ℕ) :
    (∑ i, weights a f n i) ≤
      (N : ℚ) * (3/4 : ℚ) ^ mistakes (learner a f) f n := by
  induction n with
  | zero => simp [weights, mistakes]
  | succ n ih =>
    have hs := step (weights a f n) (a n) (f n)
      (fun i => le_of_lt (positive a f n i))
    simp only [weights, mistakes]
    by_cases h : learner a f n = f n
    · have hh : predict (weights a f n) (a n) = f n := h
      simp only [hh, ite_true, mul_one] at hs
      simpa only [h, ite_true, Nat.add_zero] using hs.trans ih
    · have hh : predict (weights a f n) (a n) ≠ f n := h
      rw [ite_eq_right hh] at hs
      rw [ite_eq_right h, pow_succ]
      exact hs.trans (by nlinarith)

private theorem disagreement_triangle (a b c : ℕ → Bool) (n : ℕ) :
    mistakes a c n ≤ mistakes a b n + mistakes b c n := by
  induction n with
  | zero => simp [mistakes]
  | succ n ih =>
    simp only [mistakes]
    cases a n <;> cases b n <;> cases c n <;> simp_all <;> omega

private theorem mistakes_symm (a b : ℕ → Bool) (n : ℕ) :
    mistakes a b n = mistakes b a n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [mistakes, ih]; simp only [eq_comm]

/-- Actual truth is used only in the evaluation, not in the online update. -/
theorem performance : Performance := by
  intro N a f truth n i
  have lower : weights a f n i ≤ ∑ j, weights a f n j :=
    Finset.single_le_sum (fun j _ => le_of_lt (positive a f n j)) (Finset.mem_univ i)
  refine ⟨?_, disagreement_triangle (learner a f) f truth n, ?_⟩
  · rw [← expert_weight]
    exact lower.trans (potential a f n)
  · have h := disagreement_triangle (fun t => a t i) truth f n
    simpa only [mistakes_symm truth f n] using h

/-- Corruption costs at most k disagreements for either stream comparison. -/
theorem robust_performance : RobustPerformance := by
  intro N a f truth n k i hk
  obtain ⟨hp, hl, he⟩ := performance N a f truth n i
  have hexp : mistakes (fun t => a t i) f n ≤ mistakes (fun t => a t i) truth n + k := by omega
  have hlexp : mistakes (learner a f) truth n - k ≤ mistakes (learner a f) f n := by omega
  exact (pow_le_pow_of_le_one (by norm_num) (by norm_num) hexp).trans
    (hp.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) hlexp) (Nat.cast_nonneg N)))

/-- Nonzero expert error and nonzero feedback corruption are both allowed. -/
theorem two_expert_budget : TwoExpertBudget := by
  intro a f truth n i he hk
  have h := robust_performance 2 a f truth n 1 i hk
  by_contra bad
  have hm : 10 ≤ mistakes (learner a f) truth n - 1 := by omega
  have hleft : (1/2 : ℚ)^3 ≤ (1/2 : ℚ)^(mistakes (fun t => a t i) truth n + 1) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hright : (3/4 : ℚ)^(mistakes (learner a f) truth n - 1) ≤ (3/4 : ℚ)^10 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hm
  norm_num at hleft hright h
  linarith

private theorem traces : TraceControls := by
  have mass0 : ∀ w t, mass w (traceAdvice t) false = w 0 := by
    intro w t
    simp only [mass, Fin.sum_univ_succ]
    norm_num [traceAdvice]
  have mass1 : ∀ w t, mass w (traceAdvice t) true = w 1 := by
    intro w t
    simp only [mass, Fin.sum_univ_succ]
    norm_num [traceAdvice]
  have l0 : learner traceAdvice traceFeedback 0 = true := by
    simp only [learner, predict, mass0, mass1]
    norm_num [weights]
  have l1 : learner traceAdvice traceFeedback 1 = false := by
    simp only [learner, predict, mass0, mass1]
    norm_num [weights, update, traceAdvice, traceFeedback]
  have l2 : learner traceAdvice traceFeedback 2 = true := by
    simp only [learner, predict, mass0, mass1]
    norm_num [weights, update, traceAdvice, traceFeedback]
  refine ⟨l0, l1, l2,
    by norm_num [weights, update, traceAdvice, traceFeedback],
    by norm_num [weights, update, traceAdvice, traceFeedback],
    by norm_num [mistakes, l0, l1, l2],
    by decide, by decide, ?_⟩
  intro h
  have inv := (TruthCore.Results.Logic.CorrectionCriterion.characterization.1
    Bool _ _ _).mp h
  have bad : false = true := (inv false true rfl).mpr rfl
  cases bad

private theorem misleading : Misleading := by
  intro n
  have h0 := expert_weight traceAdvice (fun _ => false) (n+1) 0
  have h1 := expert_weight traceAdvice (fun _ => false) (n+1) 1
  have count0 : ∀ t, mistakes (fun t => traceAdvice t 0) (fun _ => false) t = 0 := by
    intro t; induction t with
    | zero => rfl
    | succ t ih => simp only [mistakes]; norm_num [traceAdvice]; exact ih
  have count1 : ∀ t, mistakes (fun t => traceAdvice t 1) (fun _ => false) t = t := by
    intro t; induction t with
    | zero => rfl
    | succ t ih => simp only [mistakes]; norm_num [traceAdvice]; exact ih
  rw [count0] at h0
  rw [count1] at h1
  have hpow : (1/2 : ℚ) ^ (n+1) < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  simp only [learner, predict, mass, Fin.sum_univ_succ, Finset.univ_eq_empty,
    Finset.sum_empty, traceAdvice]
  norm_num at h0 ⊢
  rw [h0, h1]
  exact hpow

private theorem recovery : Recovery := by
  intro n
  constructor
  · induction n with
    | zero => norm_num [mistakes, learner, predict, mass, Fin.sum_univ_succ, weights, traceAdvice]
    | succ n ih =>
      change mistakes (learner traceAdvice (fun _ => false)) (fun _ => false) (n+1) +
        (if learner traceAdvice (fun _ => false) (n+1) = false then 0 else 1) = 1
      rw [misleading n]
      simpa only [ite_true, Nat.add_zero] using ih
  · have count : ∀ t, mistakes (fun _ => true) (fun _ => false) t = t := by
      intro t
      induction t with
      | zero => rfl
      | succ t ih => simp [mistakes, ih]
    exact count (n+1)

/-- Weighted-majority correction competes with each expert despite arbitrary
feedback; corruption transfers the mistake count, without certifying its bound
or giving feedback normative authority. The exact-access and accuracy results
are imported unchanged, not restated as assumptions. -/
theorem certificate : Certificate := by
  exact ⟨performance, robust_performance, two_expert_budget, traces, misleading, recovery,
    TruthCore.Results.Logic.CorrectionCriterion.characterization,
    TruthCore.Results.Logic.EpistemicAccuracy.certificate,
    TruthCore.Results.Logic.EpistemicAccuracy.Statewise.dominance,
    TruthCore.Results.Logic.TranscendentalPractice.InquiryAccess.boundary⟩

end TruthCore.Results.Logic.FallibleCorrection
