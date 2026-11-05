module

public import TruthCore.Ethics.PopulationComparability
public import TruthCore.Results.Ethics.PopulationScoring.Solution
public import Mathlib.Tactic.Linarith

@[expose] public section
namespace TruthCore.Results.Ethics.PopulationComparability
open TruthCore.Ethics.PopulationComparability
open TruthCore.Ethics.PopulationScoring

/-- Reuse the old equal-count comparison and the checked list-summary bridge. -/
theorem mean_iff (x y : Pair) :
    total (population x) < total (population y) ↔
      mean (population x) < mean (population y) := by
  have hx : 0 < (population x).length := by simp [population]
  have hy : 0 < (population y).length := by simp [population]
  have h := TruthCore.Results.Ethics.PopulationAggregation.controls.2.2.1
    (summary (population x) hx) (summary (population y) hy) (by rfl)
  rw [TruthCore.Results.Ethics.PopulationScoring.summary_total,
    TruthCore.Results.Ethics.PopulationScoring.summary_total] at h
  exact h

theorem all_iff (x y : Pair) (c : ℝ) :
    AllPrefer c x y ↔ total (population x) < total (population y) := by
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, (mean_iff x y).mp h, ?_⟩
    simp only [total, critical, score, population, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, id_eq] at h ⊢
    linarith

/-- Any opposing individual differences admit BOTH collective orientations.
Explicit positive weights avoid division, zero-denominator and existence tricks. -/
theorem reversal (x y : Pair) (u v : ℝ) (h₁ : x.1 < y.1) (h₂ : y.2 < x.2) :
    ∃ a b a' b', 0 < a ∧ 0 < b ∧ 0 < a' ∧ 0 < b' ∧
      ∀ c, AllPrefer c (reframe a b u v x) (reframe a b u v y) ∧
        AllPrefer c (reframe a' b' u v y) (reframe a' b' u v x) := by
  have hp : 0 < (y.1 - x.1) * (x.2 - y.2) :=
    mul_pos (sub_pos.mpr h₁) (sub_pos.mpr h₂)
  refine ⟨2 * (x.2 - y.2), y.1 - x.1, x.2 - y.2, 2 * (y.1 - x.1),
    by linarith, by linarith, by linarith, by linarith, ?_⟩
  intro c
  constructor <;> apply (all_iff _ _ c).mpr <;>
    simp only [total, score, population, reframe, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, id_eq] <;> nlinarith

/-- Conditional representation controls, not vindication of any policy. -/
theorem controls : TruthCore.Ethics.PopulationComparability.Controls := by
  refine ⟨all_iff, ?_, reversal, ?_, ?_⟩
  · intro a b u v x y ha hb
    dsimp [reframe]
    constructor <;> constructor <;> intro h <;> nlinarith
  · intro x y a u v c ha
    rw [all_iff, all_iff]
    simp only [total, score, population, reframe, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, id_eq]
    constructor <;> intro h <;> nlinarith
  · intro x y a b u v c ha hb h₁ h₂ hs
    apply (all_iff _ _ c).mpr
    simp only [total, score, population, reframe, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, id_eq]
    rcases hs with hs | hs
    · have hp := mul_pos ha (sub_pos.mpr hs)
      have hq := mul_nonneg (le_of_lt hb) (sub_nonneg.mpr h₂)
      nlinarith
    · have hp := mul_nonneg (le_of_lt ha) (sub_nonneg.mpr h₁)
      have hq := mul_pos hb (sub_pos.mpr hs)
      nlinarith

end TruthCore.Results.Ethics.PopulationComparability
