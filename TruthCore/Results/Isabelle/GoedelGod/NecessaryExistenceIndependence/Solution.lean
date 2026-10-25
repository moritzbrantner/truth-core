import TruthCore.Isabelle.AFP.GoedelGod

namespace TruthCore.Results.Isabelle.GoedelGod.NecessaryExistenceIndependence

open TruthCore.Modal
open TruthCore.Isabelle.AFP.GoedelGod

/-- The two worlds both access each other. Positivity is evaluated at the
designated world `false`, regardless of the world at which it is asserted.
The property of holding only at `false` is an essence there but has no
instance at `true`, so `NE` fails at the designated world. -/
theorem checks : NecessaryExistencePositivityIndependent := by
  let F : Frame Bool := ⟨fun _ _ => True⟩
  let P : Positivity Bool Unit := fun Φ _ => Φ () false
  have hNoNE : ¬ NecessaryExistence F () false := by
    intro hNE
    have hEss : Essence F (fun _ v => v = false) () false := by
      constructor
      · rfl
      · intro Ψ hΨ v _ y hΦ
        cases v with
        | false =>
          cases y
          exact hΨ
        | true => exact Bool.noConfusion hΦ
    obtain ⟨y, hy⟩ := hNE (fun _ v => v = false) hEss true trivial
    exact Bool.noConfusion hy
  have hNoGodAtTrue : ¬ ∃ x, GodLike P x true := by
    rintro ⟨x, hG⟩
    have hAtFalse : P (fun _ v => v = false) true := rfl
    exact Bool.noConfusion (hG (fun _ v => v = false) hAtFalse)
  refine ⟨F, P, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro _
    trivial
  · intro _ _ _
    trivial
  · intro _ _ _ _ _
    trivial
  · intro _ Φ hNeg hPos
    exact hNeg hPos
  · intro _ Φ hNotPos
    exact hNotPos
  · intro _ Φ Ψ hPos hBox
    exact hBox false trivial () hPos
  · intro _ Φ hPos
    exact hPos
  · intro _ Φ hPos _ _
    exact hPos
  · intro w
    exact ⟨false, trivial, (), fun Φ hPos => hPos⟩
  · intro hA5
    exact hNoNE (hA5 false)
  · intro hT3
    exact hNoGodAtTrue (hT3 false true trivial)

end TruthCore.Results.Isabelle.GoedelGod.NecessaryExistenceIndependence
