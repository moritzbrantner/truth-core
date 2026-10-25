import TruthCore.Refutations.QuasiRealism
namespace TruthCore.Results.Comparison.QuasiRealism.DeviatesOnRobustTruth
open TruthCore.English.VanRoojen
open TruthCore.Refutations.QuasiRealism
theorem quasiRealismDeviatesOnRobustTruth {Sentence : Type}
    (Moral TruthApt RobustlyTruthApt : Sentence → Prop) (p : Sentence)
    (hQuasiRealism : QuasiRealistMinimalTruthAptReading Moral TruthApt RobustlyTruthApt)
    (hMoral : GeachMinorPremiseIsMoralReading Moral p) :
    QuasiRealistRobustTruthAnswerDeviates Moral TruthApt RobustlyTruthApt := by
  sorry
end TruthCore.Results.Comparison.QuasiRealism.DeviatesOnRobustTruth
