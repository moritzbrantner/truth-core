import TruthCore.Refutations.QuasiRealism
namespace TruthCore.Results.Comparison.QuasiRealism.AntirealistOrderSustainsRobustTruthDeviation
open TruthCore.English.VanRoojen
open TruthCore.Refutations.QuasiRealism
theorem antirealistOrderSustainsRobustTruthDeviation {Sentence : Type}
    (Moral SurfaceAssertoric DisciplinedUse TruthApt RobustlyTruthApt
      TalkExplainsTruth TruthExplainsTalk : Sentence → Prop)
    (hSufficiency :
      MinimalConstraintsSufficeForTruthAptnessReading SurfaceAssertoric DisciplinedUse TruthApt)
    (hMoralMeets :
      MoralSentencesMeetMinimalConstraintsReading Moral SurfaceAssertoric DisciplinedUse)
    (hRobustExplains :
      RobustMoralTruthIsExplanatoryReading Moral RobustlyTruthApt TruthExplainsTalk)
    (hAntirealistOrder : AntirealistOrderOfExplanationReading Moral TalkExplainsTruth)
    (hAsymmetric : ExplanatoryOrderAsymmetric Moral TalkExplainsTruth TruthExplainsTalk) :
    QuasiRealistMinimalTruthAptReading Moral TruthApt RobustlyTruthApt := by
  sorry
end TruthCore.Results.Comparison.QuasiRealism.AntirealistOrderSustainsRobustTruthDeviation
