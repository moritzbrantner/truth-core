import TruthCore.Teleonomy.Mechanisms
namespace TruthCore.Results.Comparison.Teleonomy.BiologicalNonlivingScope
open TruthCore.Teleonomy
open TruthCore.Results.Aquinas.SummaTheologiae.QuintaViaModels

theorem biologicalNonlivingScope : BiologicalToNonlivingFails := by
  refine ⟨by exact ⟨rfl, rfl, rfl, rfl⟩, ?_, ?_⟩
  · exact ⟨⟨.b0, trivial⟩, fun _ hx => ⟨(), hx, trivial⟩⟩
  · intro h
    obtain ⟨_, _, _, hFalse⟩ := h .b0 trivial
    exact hFalse
end TruthCore.Results.Comparison.Teleonomy.BiologicalNonlivingScope
