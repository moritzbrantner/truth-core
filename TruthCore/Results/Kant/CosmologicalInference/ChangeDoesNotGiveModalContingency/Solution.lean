module

public import TruthCore.German.Kant.CosmologicalInference

@[expose] public section

namespace TruthCore.Results.Kant.CosmologicalInference.ChangeDoesNotGiveModalContingency
open TruthCore.German.Kant.CosmologicalInference

theorem changeDoesNotGiveModalContingency :
    ChangeDoesNotGiveModalContingency := by
  let frame : TruthCore.Modal.Frame Bool := { access := fun _ _ => True }
  let state : Bool → Bool → Prop := fun _ time => time = false
  refine ⟨frame, state, fun _ _ => True.intro, rfl, Bool.noConfusion, ?_⟩
  rintro ⟨w, _, hnot⟩
  exact hnot rfl

end TruthCore.Results.Kant.CosmologicalInference.ChangeDoesNotGiveModalContingency
