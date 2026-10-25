import TruthCore.German.Kant.CosmologicalInference

namespace TruthCore.Results.Kant.CosmologicalInference.WithholdingCompatibleWithBeing
open TruthCore.German.Kant.CosmologicalInference

theorem withholdingCompatibleWithBeing :
    WithholdingCompatibleWithBeing := by
  let family : Bool → Ontic Bool Bool := fun s => {
    frame := { access := fun _ _ => True }
    ExistsAt := fun w x => s = true ∨ w = x
    Causes := fun _ _ _ => False }
  have positive : NecessaryBeing (family true) false :=
    ⟨false, Or.inl rfl, fun _ _ => Or.inl rfl⟩
  have negative : ¬NecessaryBeing (family false) false := by
    rintro ⟨x, _, hn⟩
    have hf : false = x := (hn false True.intro).resolve_left Bool.noConfusion
    have ht : true = x := (hn true True.intro).resolve_left Bool.noConfusion
    exact Bool.noConfusion (hf.trans ht.symm)
  refine ⟨family, positive, ?_, ?_⟩
  · intro known
    exact negative (known false True.intro)
  · intro known
    exact known true True.intro positive

end TruthCore.Results.Kant.CosmologicalInference.WithholdingCompatibleWithBeing
