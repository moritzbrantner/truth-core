import TruthCore.Comparison.Resurrection
namespace TruthCore.Results.Comparison.Resurrection.CatholicConsistent
open TruthCore.History.Resurrection
open TruthCore.Comparison.Resurrection
/-! A finite model of the limited commitments, not a reconstruction of history. -/
theorem consistent : CatholicConsistent := by
  refine ⟨model .risenEncounter true true true false false, ?_⟩
  unfold Catholic
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · exact ⟨rfl, rfl⟩
  constructor
  · exact ⟨rfl, rfl, rfl, rfl⟩
  constructor
  · exact ⟨rfl, rfl⟩
  constructor
  · exact ⟨rfl, rfl⟩
  exact ⟨⟨true, rfl⟩, True.intro, True.intro, True.intro, rfl, rfl, rfl, rfl, rfl, rfl⟩
end TruthCore.Results.Comparison.Resurrection.CatholicConsistent
