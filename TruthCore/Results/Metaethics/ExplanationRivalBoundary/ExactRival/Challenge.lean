import TruthCore.Metaethics.ExplanationRivalBoundary
namespace TruthCore.Results.Metaethics.ExplanationRivalBoundary.ExactRival
open TruthCore.Metaethics.ExplanationRivalBoundary
open TruthCore.English.VanRoojen
open TruthCore.Refutations.QuasiRealism
theorem exactRival {Sentence : Type} (Moral TalkToTruth TruthToTalk : Sentence → Prop) (p : Sentence)
    (hAnti : AntirealistOrderOfExplanationReading Moral TalkToTruth)
    (hAsym : ExplanatoryOrderAsymmetric Moral TalkToTruth TruthToTalk)
    (hMoral : GeachMinorPremiseIsMoralReading Moral p) : NotRealistOrder Moral TruthToTalk := by
  sorry
end TruthCore.Results.Metaethics.ExplanationRivalBoundary.ExactRival
