import TruthCore.Causality.BoundedPastResource
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

namespace TruthCore.Results.Causality.BoundedPastResource
open TruthCore.Causality.BoundedPastResource

/-- A real stock cannot have both a lower bound on a beginningless integer
past and one uniform positive increment at every forward unit step. This is a
conditional constraint on that profile, not a claim that physical entropy or
the universe satisfies these assumptions. -/
theorem noUniformGrowth (S : Int → ℝ) (now : Int) (ε L : ℝ)
    (hPositive : PositiveStep ε)
    (hLower : PastLowerBound S now L)
    (hGrowth : UniformPastGrowth S now ε) :
    TruthCore.Logic.ConfigurationFalse := by
  have hWalk : ∀ n : Nat, S (now - (n : Int)) + (n : ℝ) * ε ≤ S now := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hTime : now - ((n + 1 : Nat) : Int) < now := by omega
      have hStep := hGrowth _ hTime
      have hIndex : now - ((n + 1 : Nat) : Int) + 1 = now - (n : Int) := by omega
      rw [hIndex] at hStep
      simp only [Nat.cast_succ] at ⊢
      simp only [Nat.cast_add, Nat.cast_one] at hStep
      nlinarith
  have hBudget : ∀ n : Nat, (n : ℝ) * ε ≤ S now - L := by
    intro n
    have hPast : now - (n : Int) ≤ now := by omega
    have hStock := hLower _ hPast
    have hWalkN := hWalk n
    linarith
  obtain ⟨n, hn⟩ := exists_nat_gt ((S now - L) / ε)
  have hPositiveReal : 0 < ε := hPositive
  have hExceeds : S now - L < (n : ℝ) * ε :=
    (div_lt_iff₀ hPositiveReal).mp hn
  exact (not_lt_of_ge (hBudget n)) hExceeds

end TruthCore.Results.Causality.BoundedPastResource
