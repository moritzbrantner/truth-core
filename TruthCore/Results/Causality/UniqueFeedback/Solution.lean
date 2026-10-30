import TruthCore.Causality.UniqueFeedback

namespace TruthCore.Results.Causality.UniqueFeedback
open TruthCore.Causality.UniqueFeedback

/-- Exhaust the four states. Three violate a local equation; the remaining
state satisfies both. No explanatory bridge or observed bit is assumed. -/
theorem controls : Controls := by
  refine ⟨by unfold Sensitive; decide, by unfold Consistent; decide, ?_⟩
  intro state h
  rcases state with ⟨a, b⟩
  cases a <;> cases b
  · exact Bool.noConfusion h.1
  · exact Bool.noConfusion h.2
  · rfl
  · exact Bool.noConfusion h.1

end TruthCore.Results.Causality.UniqueFeedback
