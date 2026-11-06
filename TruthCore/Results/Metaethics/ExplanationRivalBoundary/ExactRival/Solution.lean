module

public import TruthCore.Metaethics.ExplanationRivalBoundary

@[expose] public section
namespace TruthCore.Results.Metaethics.ExplanationRivalBoundary.ExactRival
open TruthCore.Metaethics.ExplanationRivalBoundary
open TruthCore.English.VanRoojen
open TruthCore.Refutations.QuasiRealism
theorem exactRival {Sentence : Type} (Moral TalkToTruth TruthToTalk : Sentence → Prop) (p : Sentence)
    (hAnti : AntirealistOrderOfExplanationReading Moral TalkToTruth)
    (hAsym : ExplanatoryOrderAsymmetric Moral TalkToTruth TruthToTalk)
    (hMoral : GeachMinorPremiseIsMoralReading Moral p) : NotRealistOrder Moral TruthToTalk := by
  intro hRealist
  exact hAsym p hMoral (hAnti p hMoral) (hRealist p hMoral)
end TruthCore.Results.Metaethics.ExplanationRivalBoundary.ExactRival
