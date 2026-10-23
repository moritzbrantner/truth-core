import TruthCore.English.OConnor.Metaethics
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3Evil
namespace TruthCore.Results.Comparison.ProblemOfEvil.ExternalPremiseVsEmotivism
open TruthCore.English.OConnor
open TruthCore.Latin.Aquinas.SummaTheologiae
theorem externalPremiseContradictsEmotivism {Sentence : Type}
    (SaysSomethingBad Moral TruthApt Holds : Sentence → Prop) (evilPremise : Sentence)
    (hEmotivism : MoralStatementsLackTruthValueReading Moral TruthApt)
    (hNoTruth : LackingTruthValueExcludesTruthReading TruthApt Holds)
    (hBadIsMoral : BadnessAscriptionsAreMoralReading SaysSomethingBad Moral)
    (hSaysBad : EvilPremiseSaysSomethingBadReading SaysSomethingBad evilPremise)
    (hExternal : EvilPremiseAssertedReading Holds evilPremise) :
    False := by
  sorry
end TruthCore.Results.Comparison.ProblemOfEvil.ExternalPremiseVsEmotivism
