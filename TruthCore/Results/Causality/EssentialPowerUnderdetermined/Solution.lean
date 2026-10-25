import TruthCore.Causality.EssentialPower
import Lean.Elab.Tactic.Omega

namespace TruthCore.Results.Causality.EssentialPowerUnderdetermined
open TruthCore.Causality

/-- The successor relation admits distinct all-on/all-off solutions. For
each cut, retaining all activity upstream of the cut while extinguishing
the cut node and everything downstream also satisfies the transmission
equations. This establishes counterfactual dependence in a model, not
the actual metaphysical possibility of a causally infinite per se chain. -/
theorem essentialPowerUnderdetermined : EssentialPowerUnderdetermined := by
  refine ⟨(fun y x => y = x + 1), (fun _ => True), (fun _ => False),
    ?_, ?_, ?_, trivial, (fun h => h), ?_, ?_⟩
  · intro n
    rfl
  · intro n
    constructor
    · intro _
      exact ⟨n + 1, rfl, trivial⟩
    · intro _
      trivial
  · intro n
    constructor
    · intro h
      exact h.elim
    · rintro ⟨_, _, h⟩
      exact h
  · intro cut
    refine ⟨(fun n => cut < n), ?_, ?_, ?_⟩
    · intro n
      constructor
      · intro hAbove
        refine ⟨n + 1, ⟨rfl, ?_⟩, ?_⟩
        · omega
        · omega
      · rintro ⟨y, ⟨hLink, hNotCut⟩, hAbove⟩
        subst y
        omega
    · intro n hDownstream hActive
      omega
    · intro n hUpstream
      exact hUpstream
  · exact successorChainNotWellFounded

end TruthCore.Results.Causality.EssentialPowerUnderdetermined
