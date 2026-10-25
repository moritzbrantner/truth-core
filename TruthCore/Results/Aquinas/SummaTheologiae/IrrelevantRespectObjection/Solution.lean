import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3Interpretation
namespace TruthCore.Results.Aquinas.SummaTheologiae.IrrelevantRespectObjection
open TruthCore.Latin.Aquinas.SummaTheologiae
/-- The irrelevant-respect objection is jointly satisfiable with the strong
premises and does not block their conclusion, so it leaves the strong-reading
*prima via* standing. Both premises are premise-free results of their own
(`PrimaViaFacts.StrongPremisesCompatibleWithObjection`,
`PrimaViaFacts.StrongReadingYields`); so are this result's limits
(`PrimaViaFacts.ObjectionExposesWeakGap`, `PrimaViaFacts.StrongPremisesEntailWeak`,
`PrimaViaFacts.AbsoluteEntailsRelative`). -/
theorem irrelevantRespectObjectionLeavesStrongStanding
    (hCompatible : StrongPremisesCompatibleWithIrrelevantRespectObjection)
    (hStrong : StrongReadingYieldsUnmovedMover) :
    IrrelevantRespectObjectionLeavesStrongStanding :=
  ⟨hCompatible, fun M hPremises _ => hStrong M hPremises⟩
end TruthCore.Results.Aquinas.SummaTheologiae.IrrelevantRespectObjection
