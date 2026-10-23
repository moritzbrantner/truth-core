import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3Interpretation
import TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaModels
namespace TruthCore.Results.Aquinas.SummaTheologiae.IrrelevantRespectObjection
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaModels
/-- The irrelevant-respect objection is jointly satisfiable with the strong
premises and does not block their conclusion, so it leaves the strong-reading
*prima via* standing. -/
theorem irrelevantRespectObjectionLeavesStrongStanding
    (hCompatible : StrongPremisesCompatibleWithIrrelevantRespectObjection)
    (hStrong : StrongReadingYieldsUnmovedMover) :
    IrrelevantRespectObjectionLeavesStrongStanding :=
  ⟨hCompatible, fun M hPremises _ => hStrong M hPremises⟩
/-- Discharges `hCompatible` by the finite `strongModel`. -/
theorem strongPremisesCompatibleWithIrrelevantRespectObjection :
    StrongPremisesCompatibleWithIrrelevantRespectObjection :=
  ⟨strongModel, strongModel_premises, strongModel_objection⟩
/-- The same objection does expose the weaker reading's gap (`weakModel`). -/
theorem irrelevantRespectObjectionExposesWeakGap :
    IrrelevantRespectObjectionExposesWeakGap :=
  ⟨weakModel, weakModel_premises, weakModel_objection, weakModel_no_unmoved_mover⟩
/-- Limit of the result: the strong premises entail the weak ones, so an
objection that falsifies a weak premise falsifies a strong premise too. -/
theorem strongPremisesEntailWeakPremises : StrongPremisesEntailWeakPremises := by
  intro M ⟨hSense, hPotency, hAct, hReduction, hNotBoth, hPerSe, hRegress⟩
  exact ⟨hSense, hPotency, hAct, hReduction, hNotBoth,
    fun y x r r' hDistinct hMoves hMoved _ => hPerSe y x r hDistinct hMoves ⟨r', hMoved⟩,
    hRegress⟩
/-- Limit of the result: the absolute conclusion entails the relative one, so an
objection that falsifies the relative conclusion falsifies the absolute one too. -/
theorem absoluteConclusionEntailsRelative : AbsoluteConclusionEntailsRelative := by
  intro M hAbsolute hNoRelative
  apply hAbsolute
  intro ⟨f, ⟨x, r, hMoves⟩, hUnmoved⟩
  exact hNoRelative ⟨f, x, r, hMoves, fun r' h => hUnmoved r' h.1⟩
end TruthCore.Results.Aquinas.SummaTheologiae.IrrelevantRespectObjection
