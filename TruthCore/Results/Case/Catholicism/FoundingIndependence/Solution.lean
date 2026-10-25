import TruthCore.Case.Catholicism.FoundingIndependence
namespace TruthCore.Results.Case.Catholicism.FoundingIndependence
open TruthCore.Case.Catholicism
open TruthCore.Case.Catholicism.FoundingIndependence
open TruthCore.History.Resurrection
open TruthCore.Comparison.Resurrection
theorem independent : LocalInputsDoNotForceFounding := by
  refine ⟨witness, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r; rfl
  · intro _; rfl
  · intro _; rfl
  · intro _ _ _; exact ⟨rfl, rfl, rfl, rfl⟩
  · intro _; exact ⟨rfl, rfl⟩
  · intro _ _ _; exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩,
      ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨true, rfl⟩, True.intro,
      True.intro, True.intro, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro _ _; trivial
  · intro _ _; trivial
  · exact ⟨(), True.intro, True.intro⟩
  · intro h
    exact h true rfl True.intro True.intro True.intro rfl () True.intro True.intro

end TruthCore.Results.Case.Catholicism.FoundingIndependence
