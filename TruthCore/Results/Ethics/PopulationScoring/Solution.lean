module

public import TruthCore.Ethics.PopulationScoring
public import TruthCore.Results.Ethics.PopulationAggregation.Solution
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace TruthCore.Results.Ethics.PopulationScoring
open TruthCore.Ethics.PopulationScoring

theorem score_replicate (f : ℝ → ℝ) (n : Nat) (w : ℝ) :
    score f (List.replicate n w) = (n : ℝ) * f w := by
  simp [score, nsmul_eq_mul]

theorem summary_total (p : Population) (h : 0 < p.length) :
    (summary p h).total = total p := by
  have hn : (p.length : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt h
  simp [summary, TruthCore.Ethics.PopulationAggregation.Profile.total, mean,
    mul_div_cancel₀ _ hn]

/-- Consume the exact existing summary theorem, then realize its chosen finite
count as a list of identical individual scores. No feasibility bridge is proved. -/
theorem replication (f : ℝ → ℝ) (value : Population → ℝ)
    (ha : Additive f value) (p : Population) (w : ℝ) (hw : 0 < f w) :
    ∃ n : Nat, 0 < n ∧ value p < value (List.replicate n w) := by
  let b : TruthCore.Ethics.PopulationAggregation.Profile :=
    ⟨1, by decide, max (value p) (f w) + 1⟩
  have hl : f w < b.mean := by
    dsimp [b]
    linarith [le_max_right (value p) (f w)]
  obtain ⟨q, hq, _, htotal⟩ :=
    TruthCore.Results.Ethics.PopulationAggregation.controls.1 b (f w) hw hl
  refine ⟨q.count, q.nonempty, ?_⟩
  rw [ha (List.replicate q.count w), score_replicate]
  have hb : value p < b.total := by
    simp only [b, TruthCore.Ethics.PopulationAggregation.Profile.total, Nat.cast_one, one_mul]
    linarith [le_max_left (value p) (f w)]
  simpa [TruthCore.Ethics.PopulationAggregation.Profile.total, hq] using
    lt_trans hb htotal

theorem low_replication (f : ℝ → ℝ) (value : Population → ℝ)
    (ha : Additive f value) (hp : PositiveLifeScore f) (p : Population)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ w, 0 < w ∧ w < δ ∧ ∃ n : Nat, 0 < n ∧
      value p < value (List.replicate n w) := by
  refine ⟨δ / 2, by linarith, by linarith, ?_⟩
  exact replication f value ha p _ (hp _ (by linarith))

/-- Ordinary total scoring instantiates the generic obstruction without any
additional ethical premise; its normative authority remains open. -/
theorem total_low_replication (p : Population) (δ : ℝ) (hδ : 0 < δ) :
    ∃ w, 0 < w ∧ w < δ ∧ ∃ n : Nat, 0 < n ∧
      total p < total (List.replicate n w) :=
  low_replication id total (fun _ => rfl) (fun _ h => h) p δ hδ

theorem mean_replicate (n : Nat) (w : ℝ) (hn : 0 < n) :
    mean (List.replicate n w) = w := by
  have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  simp [mean, total, score_replicate, hnr]

theorem total_append (p q : Population) : total (p ++ q) = total p + total q := by
  simp [total, score, List.map_append, List.sum_append]

theorem critical_append (p : Population) (c w : ℝ) :
    critical c (p ++ [w]) = critical c p + (w - c) := by
  simp [critical, score, List.map_append, List.sum_append]

theorem addition (p : Population) (w : ℝ) (hn : 0 < p.length)
    (hw : 0 < w) (hl : w < mean p) :
    mean (p ++ [w]) < mean p ∧ total p < total (p ++ [w]) := by
  have hnreal : (0 : ℝ) < p.length := by exact_mod_cast hn
  have he : total (p ++ [w]) = total p + w := by simp [total, score]
  have hm : mean p * (p.length : ℝ) = total p := by
    simp [mean, div_mul_cancel₀ _ (ne_of_gt hnreal)]
  constructor
  · unfold mean
    rw [he]
    simp only [List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one]
    apply (div_lt_div_iff₀ (by linarith : (0 : ℝ) < p.length + 1) hnreal).mpr
    have hl' : w * (p.length : ℝ) < total p := by nlinarith
    nlinarith
  · rw [he]
    linarith

/-- Conditional finite scoring tradeoffs; no normative choice or feasibility claim. -/
theorem controls : Controls := by
  refine ⟨summary_total, replication, low_replication, ?_, ?_, ?_, ?_, ?_, ?_,
    addition, mean_replicate, ?_, ?_⟩
  · intro f value p δ hδ ha hp hc
    obtain ⟨w, hw, hl, n, hn, hr⟩ := low_replication f value ha hp p δ hδ
    exact (not_lt_of_ge (hc w hw hl n hn)) hr
  · intro p δ w _ _ n _
    simp [score]
  · intro p hn _ w _ hl n hn'
    rw [mean_replicate n w hn']
    exact le_of_lt hl
  · rintro ⟨f, hf⟩
    have h1 := hf [2]
    have h2 := hf [2, 2]
    norm_num [mean, total, score] at h1 h2
    linarith
  · intro c hc
    constructor
    · intro w _ hl n hn
      have hnr : (0 : ℝ) < n := by exact_mod_cast hn
      change score (fun w => w - c) (List.replicate n w) ≤ critical c [c + 1]
      rw [score_replicate]
      have hr : critical c [c + 1] = 1 := by simp [critical, score]
      rw [hr]
      nlinarith
    · intro hp
      have h := hp (c / 2) (by linarith)
      linarith
  · intro p c w _ hl
    rw [critical_append]
    linarith
  · norm_num [total, score, mean]
  · intro p N w _ hw hb n hn
    rw [total, score_replicate]
    exact le_trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hn) (le_of_lt hw)) hb

end TruthCore.Results.Ethics.PopulationScoring
