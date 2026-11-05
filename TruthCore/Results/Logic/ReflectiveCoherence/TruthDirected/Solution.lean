module

public import TruthCore.Logic.ReflectiveCoherence

@[expose] public section

namespace TruthCore.Results.Logic.ReflectiveCoherence.TruthDirected

open TruthCore.Logic.ReflectiveCoherence

/-- The actual world witnesses consistency, duty-compatibility and
compatibility with every semantically necessary consequence. -/
theorem truthDirectedReflectiveDuty : TruthDirectedReflectiveDuty := by
  intro World Claim S actual duty OughtAdopt hDuty hTruthDirected
  constructor
  · intro Γ _ hOught
    exact ⟨actual, hTruthDirected Γ hOught⟩
  constructor
  · intro Γ _ hOught
    exact ⟨actual, hTruthDirected Γ hOught, hDuty⟩
  · intro Γ q hOught hFollows
    exact ⟨actual, hTruthDirected Γ hOught, hFollows actual hDuty⟩

end TruthCore.Results.Logic.ReflectiveCoherence.TruthDirected
