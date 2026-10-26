import TruthCore.Causality.Supertasks

namespace TruthCore.Results.Causality.SupertaskStableEndpoint
open TruthCore.Causality

/-- The absence of a final substage does not logically exclude a separate
limit endpoint with an eventually stable output. -/
theorem supertaskStableEndpoint : EndlessStagesWithStableEndpoint := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    trivial
  · intro n
    exact ⟨n + 1, Nat.lt_succ_self n⟩
  · refine ⟨(fun _ => true), true, 0, ?_⟩
    intro n _
    rfl

end TruthCore.Results.Causality.SupertaskStableEndpoint
