import TruthCore.Causality.ChainInstantiation
namespace TruthCore.Results.Causality.ChainInstantiation
open TruthCore.Causality.ChainInstantiation
theorem controls : Controls := by
  constructor
  · intro bound
    refine ⟨?_, Nat.zero_le _, (fun _ h => h), ?_, ?_, (fun _ => trivial), ?_⟩
    · constructor
      · intro x hx
        exact ⟨fun _ => trivial, fun _ => hx⟩
      · intro y x hy hx
        exact ⟨fun h => ⟨h.1, trivial, trivial⟩, fun h => ⟨h.1, hy, hx⟩⟩
    · exact Nat.not_succ_le_self bound
    · intro y h
      have hy : y ≤ bound := h.2.1
      rw [h.1] at hy
      exact Nat.not_succ_le_self bound hy
    · intro h
      exact TruthCore.Causality.successorChainNotWellFounded
        (fun n => by
          have ha := h.apply n
          induction ha with
          | intro x _ ih =>
            constructor
            intro y hy
            exact ih y ⟨hy, trivial, trivial⟩)
  · exact ⟨(fun _ => Iff.rfl), (fun _ => Iff.rfl),
      (fun ⟨_, h⟩ => h), ⟨0, trivial⟩⟩
end TruthCore.Results.Causality.ChainInstantiation
