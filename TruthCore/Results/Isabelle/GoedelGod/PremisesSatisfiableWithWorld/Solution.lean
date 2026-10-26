import TruthCore.Isabelle.AFP.GoedelGod

namespace TruthCore.Results.Isabelle.GoedelGod.PremisesSatisfiableWithWorld
open TruthCore.Isabelle.AFP.GoedelGod

/-- The witness of `premisesJointlySatisfiable`, now with its world exhibited:
one world, one individual, universal accessibility, and a property positive
exactly when the one individual has it. -/
theorem scottPremisesSatisfiableWithWorld : ScottPremisesSatisfiableWithWorld := by
  refine ⟨Unit, Unit, ⟨fun _ _ => True⟩, fun Φ w => Φ () w, ⟨()⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w Φ hNeg hPos
    exact hNeg hPos
  · intro w Φ hNotPos
    exact hNotPos
  · intro w Φ Ψ hPos hBox
    exact hBox w trivial () hPos
  · intro w Φ hPos
    exact hPos
  · intro w Φ hPos v _
    cases v
    cases w
    exact hPos
  · intro w Φ hEssence v _
    cases v
    cases w
    exact ⟨(), hEssence.1⟩
  · intro _ _ _
    trivial

end TruthCore.Results.Isabelle.GoedelGod.PremisesSatisfiableWithWorld
