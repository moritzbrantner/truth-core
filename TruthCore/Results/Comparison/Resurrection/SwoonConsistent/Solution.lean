import TruthCore.Comparison.Resurrection
namespace TruthCore.Results.Comparison.Resurrection.SwoonConsistent
open TruthCore.History.Resurrection
open TruthCore.Comparison.Resurrection
/-! A finite model of the limited commitments, not a reconstruction of history. -/
theorem consistent : SwoonConsistent := by
  refine ⟨model .survivorEncounter false false true false true, ?_⟩
  unfold Swoon
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
  exact ⟨Bool.noConfusion, rfl, rfl, rfl, rfl⟩
end TruthCore.Results.Comparison.Resurrection.SwoonConsistent
