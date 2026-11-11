module
public import TruthCore.Mereology.LifeRestricted327
@[expose] public section
namespace TruthCore.Results.Mereology.LifeRestricted327
open TruthCore.Mereology.LifeRestricted327

theorem certificate : Certificate := by
  refine ⟨⟨rfl, rfl, rfl, rfl⟩, ?_, rfl, ?_, ?_, rfl, rfl, (fun _ => rfl), ?_, ?_⟩
  · intro h
    have impossible := congrArg State.processing h.2.1
    cases impossible
  · intro n
    induction n with
    | zero => rfl
    | succ n ih => simp only [run, ih]; rfl
  · intro n c h hn
    have eq : n = n + 1 := h.symm.trans hn
    exact (Nat.ne_of_lt (Nat.lt_succ_self n)) eq
  · intro E event hs
    exact TruthCore.Mereology.Fission1397.incompatible _ event
      ⟨rfl, Or.inl rfl⟩ ⟨rfl, Or.inr rfl⟩ hs
  · intro P carrier parts persist
    exact TruthCore.Mereology.ProcessTurnover.turnover_excludes_fixed_extension
      _ carrier parts (TruthCore.Mereology.Vitalism.scenario_has_turnover False False) persist
end TruthCore.Results.Mereology.LifeRestricted327
