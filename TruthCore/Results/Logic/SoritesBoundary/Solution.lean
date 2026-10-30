import TruthCore.Logic.SoritesBoundary
namespace TruthCore.Results.Logic.SoritesBoundary
open TruthCore.Logic.SoritesBoundary

theorem boundary_of_endpoints (n : Nat) (P : Nat → Prop) [DecidablePred P]
    (first : P 0) (last : ¬ P n) : Boundary P n := by
  induction n with
  | zero => exact False.elim (last first)
  | succ n ih =>
    by_cases h : P n
    · exact ⟨n, Nat.lt_succ_self n, h, last⟩
    · obtain ⟨k, hk, hp, hn⟩ := ih h
      exact ⟨k, Nat.lt_succ_of_lt hk, hp, hn⟩

theorem propagate (n : Nat) (P : Nat → Prop)
    (tol : Tolerance P n) (first : P 0) : P n := by
  induction n with
  | zero => exact first
  | succ n ih =>
    apply tol n (Nat.lt_succ_self n)
    exact ih (fun k hk => tol k (Nat.lt_succ_of_lt hk))

theorem certificate : Certificate := by
  refine ⟨boundary_of_endpoints, ?_, ?_, ?_⟩
  · intro n P h
    exact h.2.1 (propagate n P h.2.2 h.1)
  · refine ⟨⟨fun _ => False, id, id, fun _ _ h => h⟩,
      ⟨fun _ => True, True.intro, True.intro, fun _ _ _ => True.intro⟩,
      ⟨fun k => k = 0, rfl, ?_, ?_⟩⟩
    · exact Nat.noConfusion
    · intro tol
      exact Nat.noConfusion (tol 0 (Nat.zero_lt_succ 0) rfl)
  · refine ⟨rfl, rfl, ?_, ?_⟩
    · intro k hk
      cases k with
      | zero => exact ⟨fun h => Status.noConfusion h.2, fun h => Status.noConfusion h.1⟩
      | succ k =>
        cases k with
        | zero => exact ⟨fun h => Status.noConfusion h.1, fun h => Status.noConfusion h.1⟩
        | succ k => exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 2 k) hk)
    · intro tol
      exact Status.noConfusion (tol 0 (Nat.zero_lt_succ 1) rfl)
end TruthCore.Results.Logic.SoritesBoundary
