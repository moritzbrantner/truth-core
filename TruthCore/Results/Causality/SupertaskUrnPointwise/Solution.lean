import TruthCore.Causality.Supertasks

namespace TruthCore.Results.Causality.SupertaskUrnPointwise
open TruthCore.Causality

/-- Avoid an internal compiler-generated helper from `Nat.add_le_add_left`:
Comparator must check the same library constants in challenge and solution. -/
private theorem add_le_add_left_explicit {a b : Nat} (h : a ≤ b) (k : Nat) :
    k + a ≤ k + b := by
  induction k with
  | zero => simpa only [Nat.zero_add] using h
  | succ k ih => simpa only [Nat.succ_add] using Nat.succ_le_succ ih

/-- All fixed ball IDs eventually leave, yet arbitrary finite stages
contain as many distinct ball IDs as desired. No stage tail is empty. -/
theorem supertaskUrnPointwise : UrnPointwiseAbsenceNotUniformEmptiness := by
  refine ⟨?_, ?_, ?_⟩
  · intro ball
    refine ⟨ball, ?_⟩
    intro stage hStage hMember
    exact (Nat.not_lt_of_ge hStage) hMember.1
  · intro count
    refine ⟨count, ?_⟩
    intro offset hOffset
    constructor
    · exact Nat.lt_of_le_of_lt
        (Nat.le_add_right count offset) (Nat.lt_succ_self (count + offset))
    · calc
        count + offset + 1 = count + (offset + 1) := by simp [Nat.add_assoc]
        _ ≤ count + count := add_le_add_left_explicit (Nat.succ_le_of_lt hOffset) count
  · rintro ⟨cutoff, hEmpty⟩
    let stage := cutoff + 1
    have hPositive : 1 ≤ stage := Nat.zero_lt_succ cutoff
    have hMember : UrnResident stage (stage + 1) := by
      constructor
      · exact Nat.lt_succ_self stage
      · exact add_le_add_left_explicit hPositive stage
    exact hEmpty stage (Nat.le_succ cutoff) (stage + 1) hMember

end TruthCore.Results.Causality.SupertaskUrnPointwise
