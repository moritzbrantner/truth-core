import TruthCore.Case.Catholicism.StageOne.NecessaryIndividual.BoundedOmission
import TruthCore.Results.Case.Catholicism.StageOne.NecessaryIndividual.Alternating.Solution

namespace TruthCore.Results.Case.Catholicism.StageOne.NecessaryIndividual.BoundedOmission
open TruthCore.Case.Catholicism.StageOne.NecessaryIndividual
open TruthCore.Case.Catholicism.StageOne.NecessaryIndividual.BoundedOmission

private theorem finOne (i : Fin 1) : i = ⟨0, Nat.zero_lt_succ 0⟩ :=
  Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ i.isLt))

private theorem omitTwo (first second : Slot) : ∃ v : Slot, first ≠ v ∧ second ≠ v := by
  cases first <;> cases second <;>
    first | exact ⟨.a, by decide, by decide⟩
          | exact ⟨.b, by decide, by decide⟩
          | exact ⟨.c, by decide, by decide⟩

/-- Bounded omissions in stipulated finite profiles; no metaphysical premise
is assumed or discharged. The nullary boundary explicitly requires a successor. -/
theorem checks : Hierarchy := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro W I F present w
    constructor
    · intro h
      obtain ⟨v, hv, _⟩ := h 0 (Nat.le_refl 0) (fun i => Fin.elim0 i)
      exact ⟨v, hv⟩
    · rintro ⟨v, hv⟩ n hn selection
      have hn0 : n = 0 := Nat.eq_zero_of_le_zero hn
      subst n
      exact ⟨v, hv, fun i => Fin.elim0 i⟩
  · intro W I F present w k l hkl h n hn selection
    exact h n (Nat.le_trans hn hkl) selection
  · intro W I F present w k h n hn selection
    obtain ⟨v, hv, empty⟩ := h
    exact ⟨v, hv, fun i hi => empty ⟨selection i, hi⟩⟩
  · constructor
    · intro n hn selection
      cases n with
      | zero => exact ⟨false, trivial, fun i => Fin.elim0 i⟩
      | succ n =>
        have hn0 : n = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_succ_le_succ hn)
        subst n
        obtain ⟨v, hv, absent⟩ :=
          Alternating.checks.2.2.2.2.1 (selection ⟨0, Nat.zero_lt_succ _⟩)
        refine ⟨v, hv, ?_⟩
        intro i
        have hi := finOne i
        subst i
        exact absent
    · intro h
      obtain ⟨v, _, absent⟩ := h 2 (Nat.le_refl 2) (fun i => i.val == 1)
      cases v with
      | false => exact absent ⟨0, Nat.zero_lt_succ 1⟩ rfl
      | true => exact absent ⟨1, Nat.lt_succ_self 1⟩ rfl
  · refine ⟨(fun _ => trivial), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro n hn selection
      cases n with
      | zero => exact ⟨Slot.a, trivial, fun i => Fin.elim0 i⟩
      | succ n =>
        cases n with
        | zero =>
          obtain ⟨v, absent, _⟩ := omitTwo (selection ⟨0, Nat.zero_lt_succ _⟩) (selection ⟨0, Nat.zero_lt_succ _⟩)
          refine ⟨v, trivial, ?_⟩
          intro i
          have hi := finOne i
          subst i
          exact absent
        | succ n =>
          have hn0 : n = 0 := Nat.eq_zero_of_le_zero
            (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hn))
          subst n
          obtain ⟨v, ha, hb⟩ := omitTwo (selection ⟨0, Nat.zero_lt_succ _⟩) (selection ⟨1, Nat.lt_succ_self 1⟩)
          refine ⟨v, trivial, ?_⟩
          intro i
          obtain ⟨j, hj⟩ := i
          cases j with
          | zero => exact ha
          | succ j =>
            cases j with
            | zero => exact hb
            | succ j =>
              exact False.elim (Nat.not_lt_zero _
                (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hj)))
    · intro h
      obtain ⟨v, _, absent⟩ := h 3 (Nat.le_refl 3) (fun i => match i.val with | 0 => .a | 1 => .b | _ => .c)
      cases v with
      | a => exact absent ⟨0, Nat.zero_lt_succ 2⟩ rfl
      | b => exact absent ⟨1, Nat.lt_trans (Nat.lt_succ_self 1) (Nat.lt_succ_self 2)⟩ rfl
      | c => exact absent ⟨2, Nat.lt_succ_self 2⟩ rfl
    · intro x
      obtain ⟨v, hx, _⟩ := omitTwo x x
      exact ⟨v, trivial, hx⟩
    · exact fun v _ => ⟨v, rfl⟩
    · rintro ⟨x, hx⟩
      obtain ⟨v, absent, _⟩ := omitTwo x x
      exact absent (hx v trivial)
    · rintro ⟨v, _, empty⟩
      exact empty ⟨v, rfl⟩
end TruthCore.Results.Case.Catholicism.StageOne.NecessaryIndividual.BoundedOmission
