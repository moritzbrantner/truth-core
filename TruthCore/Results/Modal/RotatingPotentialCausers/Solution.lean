import TruthCore.Modal.NecessaryPotentialCausers
namespace TruthCore.Results.Modal.RotatingPotentialCausers
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Causality.NecessarilyUnderived
open TruthCore.Modal.ExistenceDegrees
/-- Worldwise WF cannot replace cross-world union WF in this selected profile. -/
theorem checks : TruthCore.Modal.NecessaryPotentialCausers.RotatingControl := by
  let m := TruthCore.Models.NecessarilyUnderived.rotating
  refine ⟨TruthCore.Models.NecessarilyUnderived.rotatingReflexive,
    ?_, ?_, ?_, ?_,
    TruthCore.Models.NecessarilyUnderived.rotatingWorldWellFounded,
    TruthCore.Models.NecessarilyUnderived.rotatingUnionNotWellFounded, ?_⟩
  · intro _ _; trivial
  · intro _ _; trivial
  · intro v hv y hy hne
    cases y with
    | false => exact False.elim (hne rfl)
    | true => exact ⟨false, True.intro, Or.inl ⟨rfl, rfl, rfl⟩⟩
  · intro v hv y hy hne
    cases y with
    | false => exact ⟨true, True.intro, Or.inr ⟨rfl, rfl, rfl⟩⟩
    | true => exact False.elim (hne rfl)
  · exact Bool.noConfusion
end TruthCore.Results.Modal.RotatingPotentialCausers
