import TruthCore.Causality.NecessaryBeingSurvey

namespace TruthCore.Results.Causality.NecessaryBeingCountDescent
open TruthCore.Causality.NecessaryBeingSurvey

/-- Iterate the *explicitly assumed* decrement principle four times. This
does not establish that the decrement principle is metaphysically true, nor
that the possible cause is necessary (A7c steps 4–7 are separate). -/
theorem fiveToOne (causableAtLeast : Nat → Prop)
    (hFive : FiveCausable causableAtLeast)
    (hTransfer : CountDescent causableAtLeast) :
    OneCausable causableAtLeast := by
  have hFour : causableAtLeast 4 := hTransfer 5 (by decide) hFive
  have hThree : causableAtLeast 3 := hTransfer 4 (by decide) hFour
  have hTwo : causableAtLeast 2 := hTransfer 3 (by decide) hThree
  exact hTransfer 2 (by decide) hTwo

end TruthCore.Results.Causality.NecessaryBeingCountDescent
