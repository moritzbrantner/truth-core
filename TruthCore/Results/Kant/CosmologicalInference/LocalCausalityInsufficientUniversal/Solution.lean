import TruthCore.German.Kant.CosmologicalInference

namespace TruthCore.Results.Kant.CosmologicalInference.LocalCausalityInsufficientUniversal
open TruthCore.German.Kant.CosmologicalInference

theorem localCausalityInsufficientUniversal :
    LocalCausalityInsufficientUniversal := by
  let m : Ontic Bool (Bool × Nat) := {
    frame := { access := fun _ _ => True }
    ExistsAt := fun w x => w = x.1
    Causes := fun _ y x => y.1 = x.1 ∧ y.2 = x.2 + 1 }
  refine ⟨m, (fun _ _ => True.intro), ?_, ?_, ?_⟩
  · intro w x hx
    refine ⟨(x.1, x.2 + 1), hx.1, ⟨rfl, rfl⟩, ?_⟩
    intro heq
    have hn := congrArg Prod.snd heq
    exact Nat.add_one_ne_self x.2 hn
  · refine ⟨(false, 0), rfl, true, True.intro, ?_⟩
    exact Bool.noConfusion
  · rintro ⟨x, hx, hn⟩
    have hfalse := hn false True.intro
    have htrue := hn true True.intro
    have bad : false = true := hfalse.trans htrue.symm
    exact Bool.noConfusion bad

end TruthCore.Results.Kant.CosmologicalInference.LocalCausalityInsufficientUniversal
