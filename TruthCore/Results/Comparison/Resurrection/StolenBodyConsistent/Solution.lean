import TruthCore.Comparison.Resurrection
namespace TruthCore.Results.Comparison.Resurrection.StolenBodyConsistent
open TruthCore.History.Resurrection
open TruthCore.Comparison.Resurrection
/-! A finite model of the limited commitments, not a reconstruction of history. -/
theorem consistent : StolenBodyConsistent := by
  refine ⟨model .theftAndVision false true true true false, ?_⟩
  unfold StolenBody
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
  exact ⟨Bool.noConfusion, rfl, rfl, rfl⟩
end TruthCore.Results.Comparison.Resurrection.StolenBodyConsistent
