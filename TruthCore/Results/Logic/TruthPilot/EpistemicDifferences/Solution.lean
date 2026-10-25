import TruthCore.Logic.TruthPilot
namespace TruthCore.Results.Logic.TruthPilot.EpistemicDifferences
open TruthCore.Logic.TruthPilot
/-- Explicit model separating endorsement disagreement and limited knowledge from variation in truth. -/
theorem epistemicDifferences : EpistemicDifferencesDoNotRequireRelativity := by
  refine ⟨(fun _ _ => True), (fun a _ => a = Agent.first), (fun _ _ => False), ?_, ?_, ?_⟩
  · refine ⟨Sentence.taste, rfl, ?_⟩
    intro h
    cases h
  · refine ⟨Agent.first, Sentence.logical, ?_⟩
    intro h
    exact h
  · intro F G s
    exact Iff.rfl
end TruthCore.Results.Logic.TruthPilot.EpistemicDifferences
