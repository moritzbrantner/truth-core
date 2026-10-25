import TruthCore.Logic.TruthPilot
namespace TruthCore.Results.Logic.TruthPilot.NotAllImpliesSome
open TruthCore.Logic.TruthPilot
/-- Use the proved proposition not-every-proposition-fails itself as the existential witness. Reverse implication preserves statement identity. -/
theorem notAllImpliesSome (hNotAll : NotEveryPropositionFails) : SomePropositionHolds := by
  refine ⟨NotEveryPropositionFails, ?_⟩
  exact hNotAll
end TruthCore.Results.Logic.TruthPilot.NotAllImpliesSome
