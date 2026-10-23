import TruthCore.Refutations.ProblemOfEvil
namespace TruthCore.Results.Comparison.ProblemOfEvil.ExternalPremiseVsEmotivism
open TruthCore.English.OConnor
open TruthCore.Refutations.ProblemOfEvil
theorem externalPremiseContradictsEmotivism {Sentence : Type}
    (SaysSomethingBad Moral TruthApt Holds : Sentence → Prop) (moralEvilPremise : Sentence)
    (hEmotivism : MoralStatementsLackTruthValueReading Moral TruthApt)
    (hNoTruth : LackingTruthValueExcludesTruthReading TruthApt Holds)
    (hBadIsMoral : BadnessAscriptionsAreMoralReading SaysSomethingBad Moral)
    (hSaysBad : ManMadeEvilPremiseSaysSomethingBadReading SaysSomethingBad moralEvilPremise) :
    MoralEvilPremiseNotTrue Holds moralEvilPremise := by
  sorry
end TruthCore.Results.Comparison.ProblemOfEvil.ExternalPremiseVsEmotivism
