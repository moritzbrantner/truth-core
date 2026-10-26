import TruthCore.Causality.Supertasks

namespace TruthCore.Results.Causality.SupertaskUrnPointwise
open TruthCore.Causality

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
        _ ≤ count + count := Nat.add_le_add_left (Nat.succ_le_of_lt hOffset) count
  · rintro ⟨cutoff, hEmpty⟩
    let stage := cutoff + 1
    have hPositive : 1 ≤ stage := Nat.zero_lt_succ cutoff
    have hMember : UrnResident stage (stage + 1) := by
      constructor
      · exact Nat.lt_succ_self stage
      · exact Nat.add_le_add_left hPositive stage
    exact hEmpty stage (Nat.le_succ cutoff) (stage + 1) hMember

end TruthCore.Results.Causality.SupertaskUrnPointwise
