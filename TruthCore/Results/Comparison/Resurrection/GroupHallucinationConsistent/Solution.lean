import TruthCore.Comparison.Resurrection
namespace TruthCore.Results.Comparison.Resurrection.GroupHallucinationConsistent
open TruthCore.History.Resurrection
open TruthCore.Comparison.Resurrection
/-! A finite model of the limited commitments, not a reconstruction of history. -/
theorem consistent : GroupHallucinationConsistent := by
  refine ⟨model .groupSuggestion false true false false false, ?_⟩
  unfold GroupHallucination
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
  exact ⟨Bool.noConfusion, rfl⟩
end TruthCore.Results.Comparison.Resurrection.GroupHallucinationConsistent
