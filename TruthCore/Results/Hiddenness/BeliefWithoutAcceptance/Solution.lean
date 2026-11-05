module

public import TruthCore.Comparison.Hiddenness
public import TruthCore.Hiddenness.Models

@[expose] public section

namespace TruthCore.Results.Hiddenness.BeliefWithoutAcceptance
open TruthCore.Hiddenness TruthCore.Comparison.Hiddenness

theorem beliefWithoutAcceptance : BeliefWithoutAcceptancePossible := by
  refine ⟨delayedModel, (), true, ?_, ?_⟩
  · exact Or.inl rfl
  · intro h
    exact h

end TruthCore.Results.Hiddenness.BeliefWithoutAcceptance
