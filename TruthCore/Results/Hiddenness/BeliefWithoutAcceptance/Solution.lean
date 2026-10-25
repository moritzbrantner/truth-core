import TruthCore.Comparison.Hiddenness
import TruthCore.Hiddenness.Models

namespace TruthCore.Results.Hiddenness.BeliefWithoutAcceptance
open TruthCore.Hiddenness TruthCore.Comparison.Hiddenness

theorem beliefWithoutAcceptance : BeliefWithoutAcceptancePossible := by
  refine ⟨delayedModel, (), true, ?_, ?_⟩
  · exact Or.inl rfl
  · intro h
    exact h

end TruthCore.Results.Hiddenness.BeliefWithoutAcceptance
