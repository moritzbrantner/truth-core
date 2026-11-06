module

public import TruthCore.Logic.MetaethicsTruthAptRivalBoundary
public import TruthCore.Results.Comparison.QuasiRealism.DeviatesOnRobustTruth.Solution

@[expose] public section
namespace TruthCore.Results.Logic.MetaethicsTruthAptRivalBoundary.ExactRival
open TruthCore.English.VanRoojen
open TruthCore.Logic.MetaethicsTruthAptRivalBoundary
theorem exactRival {Sentence : Type} (Moral Minimal Robust : Sentence → Prop) (p : Sentence)
    (hQuasi : QuasiRealistMinimalTruthAptReading Moral Minimal Robust)
    (hMoral : GeachMinorPremiseIsMoralReading Moral p) :
    NotRealistRobustTruthApt Moral Robust := by
  have hDeviation := TruthCore.Results.Comparison.QuasiRealism.DeviatesOnRobustTruth.quasiRealismDeviatesOnRobustTruth
    Moral Minimal Robust p hQuasi hMoral
  intro hRobust
  exact hDeviation ⟨fun _ => hRobust, fun _ => hQuasi⟩
end TruthCore.Results.Logic.MetaethicsTruthAptRivalBoundary.ExactRival
