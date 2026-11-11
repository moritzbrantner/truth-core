module

public import TruthCore.Causality.QuantitativeTransferPaths

@[expose] public section
open scoped BigOperators
namespace TruthCore.Results.Causality.QuantitativeTransferPaths
open TruthCore.Causality.QuantitativeTransferPaths

theorem finitePath : FinitePath := by
  intro V _ w s P q M hq hq1 hM hw hs _hP hbound hsum hrow hprod hbal v hv
  by_contra hn
  have decay : ∀ n : ℕ, ∀ x, (¬ ∃ u, Path w x u ∧ 0 < s u) → P x ≤ q^n * M := by
    intro n
    induction n with
    | zero => simpa using fun x _ => hbound x
    | succ n ih =>
      intro x hx
      have sx : s x = 0 := by
        have : ¬ 0 < s x := fun h => hx ⟨x, Relation.ReflTransGen.refl, h⟩
        exact le_antisymm (le_of_not_gt this) (hs x)
      have cmp : ∀ u, w x u * P u ≤ w x u * (q^n * M) := by
        intro u
        by_cases he : 0 < w x u
        · apply mul_le_mul_of_nonneg_left _ (hw x u)
          apply ih u
          rintro ⟨z, hz, hp⟩
          exact hx ⟨z, Relation.ReflTransGen.head he hz, hp⟩
        · have hz : w x u = 0 := le_antisymm (le_of_not_gt he) (hw x u)
          simp [hz]
      calc
        P x ≤ ∑' u, w x u * P u := by simpa [sx] using hbal x
        _ ≤ ∑' u, w x u * (q^n * M) := (hprod x).tsum_le_tsum cmp ((hsum x).mul_right _)
        _ = (∑' u, w x u) * (q^n * M) := tsum_mul_right
        _ ≤ q * (q^n * M) := mul_le_mul_of_nonneg_right (hrow x) (by positivity)
        _ = q^(n+1) * M := by ring
  have hz := (tendsto_pow_atTop_nhds_zero_of_lt_one hq hq1).mul_const M
  have : P v ≤ 0 := by
    have := ge_of_tendsto hz (Filter.Eventually.of_forall (fun n => decay n v hn))
    simpa using this
  linarith

theorem vanishingTail : VanishingTail := by
  intro P q M hq hbound hbal htail
  intro n
  have expand : ∀ k, P n = (∏ j ∈ Finset.range k, q (n+j)) * P (n+k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.prod_range_succ]
      rw [ih, hbal (n+k)]
      simp only [Nat.add_assoc, mul_assoc]
  have hb : ∀ k, |P n| ≤ (∏ j ∈ Finset.range k, q (n+j)) * M := by
    intro k
    rw [expand k, abs_mul, abs_of_nonneg (Finset.prod_nonneg (fun j _ => hq (n+j)))]
    exact mul_le_mul_of_nonneg_left (hbound _) (Finset.prod_nonneg (fun j _ => hq (n+j)))
  have hlim := (htail n).mul_const M
  have hz : |P n| ≤ 0 := by simpa using ge_of_tendsto hlim (Filter.Eventually.of_forall hb)
  exact abs_eq_zero.mp (le_antisymm hz (abs_nonneg _))

theorem binaryFixed : BinaryFixed := by
  refine ⟨?_, ?_, ?_⟩
  · funext v; simp [binary]; norm_num
  · funext v; simp [binary]
  · intro v; simp

theorem nonuniformFixed : NonuniformFixed := by
  have hc (n : ℕ) : 0 < chainP n ∧ chainP n ≤ 1 ∧
      0 < chainQ n ∧ chainQ n < 1 ∧ chainP n = chainQ n * chainP (n+1) := by
    dsimp [chainP, chainQ]
    push_cast
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h2 : (0 : ℝ) < (n : ℝ)+2 := by positivity
    have h3 : (0 : ℝ) < (n : ℝ)+3 := by positivity
    refine ⟨by positivity, (div_le_one h2).2 (by linarith), ?_, ?_, ?_⟩
    · have : 1 / ((n : ℝ)+2)^2 < 1 := (div_lt_one (sq_pos_of_pos h2)).2 (by nlinarith)
      linarith
    · have : 0 < 1 / ((n : ℝ)+2)^2 := by positivity
      linarith
    · field_simp; ring
  refine ⟨?_, fun n => ⟨(hc n).1, (hc n).2.1, (hc n).2.2.1, (hc n).2.2.2.1⟩⟩
  funext n
  exact (hc n).2.2.2.2.symm

theorem halfFixed : HalfFixed := by
  constructor
  · funext n; simp only [halfChain, pow_succ]; ring
  · intro M
    simpa only [show (1 : ℝ) + 1 = 2 by norm_num] using add_one_pow_unbounded_of_pos M (by norm_num : (0 : ℝ) < 1)

theorem nonuniformTail : NonuniformTail := by
  intro n k
  have hc := nonuniformFixed
  have eqn : ∀ k, chainP n = (∏ j ∈ Finset.range k, chainQ (n+j)) * chainP (n+k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.prod_range_succ, ih]
      have hh := congrFun hc.1 (n+k)
      dsimp [nonuniform] at hh
      rw [← hh]
      simp only [Nat.add_assoc, mul_assoc]
  have hp : 0 ≤ ∏ j ∈ Finset.range k, chainQ (n+j) :=
    Finset.prod_nonneg (fun j _ => le_of_lt (hc.2 (n+j)).2.2.1)
  rw [eqn k]
  exact mul_le_of_le_one_right hp (hc.2 (n+k)).2.1

theorem resourceBudget : ResourceBudget := by
  intro C R consumers resources a b hb ha
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro r hr
  rw [← Finset.sum_mul]
  exact mul_le_of_le_one_left (hb r hr) (ha r hr)

theorem conservativeCircle : ConservativeCircle := by
  constructor
  · intro v; rfl
  · norm_num [Fintype.sum_bool]
end TruthCore.Results.Causality.QuantitativeTransferPaths
