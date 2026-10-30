import TruthCore.Modal.DeonticFutureBoundary
namespace TruthCore.Results.Modal.DeonticFutureBoundary
open TruthCore.Modal TruthCore.Modal.DeonticFutureBoundary

theorem certificate : Certificate := by
  have hblocked : ¬ Can blocked false goal := by
    rintro ⟨v, hv, hg⟩
    exact Bool.noConfusion (hv.symm.trans hg)
  refine ⟨fun _ i a w => compatibility i a w, ?_, ?_⟩
  · exact ⟨fun _ => ⟨true, rfl⟩, fun _ hv => hv,
      ⟨true, True.intro, rfl⟩, hblocked⟩
  · exact ⟨(compatibility ideal broad false).mpr ⟨true, rfl, True.intro⟩,
      Bool.noConfusion, hblocked⟩
end TruthCore.Results.Modal.DeonticFutureBoundary
