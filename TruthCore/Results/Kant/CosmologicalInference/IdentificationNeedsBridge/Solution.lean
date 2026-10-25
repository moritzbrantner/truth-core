import TruthCore.German.Kant.CosmologicalInference

namespace TruthCore.Results.Kant.CosmologicalInference.IdentificationNeedsBridge
open TruthCore.German.Kant.CosmologicalInference

theorem identificationNeedsBridge :
    IdentificationNeedsBridge := by
  let m : Ontic Bool Bool := {
    frame := { access := fun _ _ => True }
    ExistsAt := fun _ _ => True
    Causes := fun _ _ _ => False }
  let p : RealityProfile Bool := { Feature := Unit, Has := fun _ _ => False }
  refine ⟨m, p, ⟨false, True.intro, fun _ _ => True.intro⟩, ?_⟩
  rintro ⟨x, _, hreal⟩
  exact hreal ()

end TruthCore.Results.Kant.CosmologicalInference.IdentificationNeedsBridge
