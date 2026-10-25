import TruthCore.Comparison.Resurrection
namespace TruthCore.Results.Comparison.Resurrection.HallucinationConsistent
open TruthCore.History.Resurrection
open TruthCore.Comparison.Resurrection
/-! A finite model of the limited commitments, not a reconstruction of history. -/
theorem consistent : HallucinationConsistent := by
  refine ⟨model .individualVision false true false false false, ?_⟩
  unfold Hallucination
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
end TruthCore.Results.Comparison.Resurrection.HallucinationConsistent
