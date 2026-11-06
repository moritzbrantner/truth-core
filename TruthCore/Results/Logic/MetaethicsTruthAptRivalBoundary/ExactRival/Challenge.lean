import TruthCore.Logic.MetaethicsTruthAptRivalBoundary
import TruthCore.Results.Comparison.QuasiRealism.DeviatesOnRobustTruth.Solution
namespace TruthCore.Results.Logic.MetaethicsTruthAptRivalBoundary.ExactRival
open TruthCore.English.VanRoojen
open TruthCore.Logic.MetaethicsTruthAptRivalBoundary
theorem exactRival {Sentence : Type} (Moral Minimal Robust : Sentence → Prop) (p : Sentence)
    (hQuasi : QuasiRealistMinimalTruthAptReading Moral Minimal Robust)
    (hMoral : GeachMinorPremiseIsMoralReading Moral p) :
    NotRealistRobustTruthApt Moral Robust := by
  sorry
end TruthCore.Results.Logic.MetaethicsTruthAptRivalBoundary.ExactRival
