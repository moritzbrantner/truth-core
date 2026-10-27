import TruthCore.English.Rowe.EvidentialEvil

namespace TruthCore.Results.Comparison.ProblemOfEvil.RoweDeductiveCore
open TruthCore.English.Rowe

/-- Rowe's deductive consequence; neither premise is discharged. -/
theorem roweDeductiveCore (s : Sig)
    (hGratuitous : GratuitousSufferingReading s)
    (hPermission : PermissionConstraintReading s) : NoTheisticBeing s := by
  obtain ⟨e, hOccurs, hIntense, hAvoid⟩ := hGratuitous
  intro hTheism
  obtain ⟨b, hKnows, hPower, hGood⟩ := hTheism
  obtain ⟨hCan, hNoCost⟩ := hAvoid b hKnows hPower
  exact hNoCost (hPermission b e hKnows hGood hOccurs hIntense hCan)

end TruthCore.Results.Comparison.ProblemOfEvil.RoweDeductiveCore
