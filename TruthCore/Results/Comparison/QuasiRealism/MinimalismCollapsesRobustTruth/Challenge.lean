import TruthCore.Refutations.QuasiRealism
namespace TruthCore.Results.Comparison.QuasiRealism.MinimalismCollapsesRobustTruth
open TruthCore.English.VanRoojen
theorem minimalismCollapsesRobustTruth {Sentence : Type}
    (Moral SurfaceAssertoric DisciplinedUse TruthApt RobustlyTruthApt : Sentence → Prop)
    (hSufficiency :
      MinimalConstraintsSufficeForTruthAptnessReading SurfaceAssertoric DisciplinedUse TruthApt)
    (hMoralMeets :
      MoralSentencesMeetMinimalConstraintsReading Moral SurfaceAssertoric DisciplinedUse)
    (hNoRobustBeyond : NoRobustTruthAptnessBeyondMinimalReading TruthApt RobustlyTruthApt) :
    RealistRobustTruthAptReading Moral RobustlyTruthApt := by
  sorry
end TruthCore.Results.Comparison.QuasiRealism.MinimalismCollapsesRobustTruth
