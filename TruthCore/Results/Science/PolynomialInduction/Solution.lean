module
public import TruthCore.Science.PolynomialInduction
public import Mathlib.Tactic.ComputeDegree
@[expose] public section
namespace TruthCore.Results.Science.PolynomialInduction
open Polynomial TruthCore.Science.PolynomialInduction
variable {K : Type*} [CommRing K] [IsDomain K]
 theorem threshold (s : Finset K) (d : ℕ) : Identifiable s d ↔ d < s.card := by
  classical
  constructor
  · intro h
    by_contra hn
    have hd : s.card ≤ d := Nat.le_of_not_gt hn
    have hm : (vanishing s).Monic := monic_prod_of_monic _ _ (by intros; exact monic_X_sub_C _)
    have he : vanishing s = 0 := h (vanishing s) 0 (by simpa [vanishing, natDegree_finsetProd_X_sub_C_eq_card] using hd) (by simp) (by
      intro x hx
      simp only [vanishing, eval_prod, eval_sub, eval_X, eval_C, eval_zero]
      exact Finset.prod_eq_zero hx (by simp))
    exact hm.ne_zero he
  · intro hd p q hp hq he
    exact eq_of_natDegree_lt_card_of_eval_eq' p q s he (lt_of_le_of_lt (max_le hp hq) hd)


open Polynomial
 theorem fresh_divergence {K : Type*} [CommRing K] [IsDomain K]
    (s : Finset K) (a : K) (ha : a ∉ s) (p : K[X]) :
    (∀ x ∈ s, (p + vanishing s).eval x = p.eval x) ∧
    (p + vanishing s).eval a ≠ p.eval a := by
  classical
  have hz : ∀ x ∈ s, (vanishing s).eval x = 0 := by
    intro x hx
    simp only [vanishing, eval_prod, eval_sub, eval_X, eval_C]
    exact Finset.prod_eq_zero hx (by simp)
  constructor
  · intro x hx; simp [hz x hx]
  · have hn : (vanishing s).eval a ≠ 0 := by
      simp only [vanishing, eval_prod, eval_sub, eval_X, eval_C]
      exact Finset.prod_ne_zero_iff.mpr (by intro x hx; exact sub_ne_zero.mpr (by intro h; exact ha (h ▸ hx)))
    simpa using hn
 theorem affine_degree {K : Type*} [CommRing K] [IsDomain K]
    (p : K[X]) (a b : K) (ha : a ≠ 0) :
    (p.comp (C a * X + C b)).natDegree = p.natDegree := by
  rw [natDegree_comp, natDegree_add_C, natDegree_C_mul_X _ ha, Nat.mul_one]
 theorem concrete :
    (∀ x ∈ ({0,1,2,3} : Finset ℚ),
      (X^2 + X*(X-1)*(X-2)*(X-3) : ℚ[X]).eval x = (X^2 : ℚ[X]).eval x) ∧
    (X^2 : ℚ[X]).eval 4 = 16 ∧
    (X^2 + X*(X-1)*(X-2)*(X-3) : ℚ[X]).eval 4 = 40 := by
  norm_num [Finset.mem_insert, Finset.mem_singleton, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X]



 theorem nonlinear :
    Function.Injective (fun x : ℝ => x + x^3) ∧
    (X + X^3 : ℝ[X]).natDegree = 3 ∧ (X : ℝ[X]).natDegree = 1 := by
  refine ⟨?_, by compute_degree; norm_num, by simp⟩
  intro x y h
  have hpos : 0 < 1 + x^2 + x*y + y^2 := by
    nlinarith [sq_nonneg (x+y), sq_nonneg x, sq_nonneg y]
  have hz : (x-y)*(1+x^2+x*y+y^2) = 0 := by nlinarith
  rcases mul_eq_zero.mp hz with hz | hz
  · linarith
  · linarith



 theorem nonlinear_surjective : Function.Surjective (fun x : ℝ => x + x^3) := by
  intro y
  let b := |y| + 1
  have hb : 0 < b := by dsimp [b]; positivity
  have hc : 0 < b^3 := pow_pos hb 3
  have hleft : (-b) + (-b)^3 ≤ y := by
    have := neg_abs_le y
    dsimp [b] at *
    nlinarith
  have hright : y ≤ b + b^3 := by
    have := le_abs_self y
    dsimp [b] at *
    nlinarith
  obtain ⟨x, _, hx⟩ := intermediate_value_Icc (show -b ≤ b by linarith)
    (show ContinuousOn (fun x : ℝ => x+x^3) (Set.Icc (-b) b) by fun_prop)
    ⟨hleft, hright⟩
  exact ⟨x, hx⟩


theorem certificate : Certificate := by
  refine ⟨fun K _ _ s d => threshold s d,
    fun K _ _ s a ha p => fresh_divergence s a ha p,
    fun K _ _ p a b ha => affine_degree p a b ha,
    concrete, ?_⟩
  exact ⟨⟨nonlinear.1, nonlinear_surjective⟩, nonlinear.2⟩
end TruthCore.Results.Science.PolynomialInduction
