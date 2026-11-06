module
public import TruthCore.Metaethics.MeaningRivalBoundary
@[expose] public section
namespace TruthCore.Results.Metaethics.MeaningRivalBoundary.Controls
open TruthCore.English.VanRoojen
open TruthCore.Refutations.Emotivism
open TruthCore.Metaethics.MeaningRivalBoundary
theorem controls : Controls := by
  constructor
  · refine ⟨(fun _ => True), (fun _ _ => ()), (fun _ _ _ => True), True.intro, ?_, ?_, True.intro, True.intro⟩
    · intro _ _ _ _
      rfl
    · intro _ _ _ _ _ _ h
      exact h
  · refine ⟨(fun _ => True), (fun _ _ => ()), (fun _ c _ => c = true), True.intro, ?_, ?_, ?_, rfl, ?_, ?_⟩
    · intro _ _ _ _
      rfl
    · intro _ _
      exact ⟨(), rfl⟩
    · intro _ _ h
      exact Bool.noConfusion h
    · intro h
      exact Bool.noConfusion h
    · intro h
      exact Bool.noConfusion (h () True.intro true false rfl () rfl)
end TruthCore.Results.Metaethics.MeaningRivalBoundary.Controls
