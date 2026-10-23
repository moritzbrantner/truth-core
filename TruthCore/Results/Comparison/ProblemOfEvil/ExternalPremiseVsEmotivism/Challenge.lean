import TruthCore.Comparison.ProblemOfEvil
import TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaModels
namespace TruthCore.Results.Comparison.ProblemOfEvil.ExternalPremiseVsEmotivism
open TruthCore.English.OConnor
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Comparison.ProblemOfEvil
theorem externalPremiseContradictsEmotivism {Sentence : Type}
    (SaysSomethingBad Moral TruthApt Holds : Sentence → Prop) (evilPremise : Sentence)
    (hEmotivism : MoralStatementsLackTruthValueReading Moral TruthApt)
    (hNoTruth : LackingTruthValueExcludesTruthReading TruthApt Holds)
    (hBadIsMoral : BadnessAscriptionsAreMoralReading SaysSomethingBad Moral)
    (hSaysBad : EvilPremiseSaysSomethingBadReading SaysSomethingBad evilPremise) :
    EvilPremiseNotTrue Holds evilPremise := by
  sorry
theorem emotivismConsistentWithBackground : ∃ s, Background s ∧ Emotivism s := by
  sorry
end TruthCore.Results.Comparison.ProblemOfEvil.ExternalPremiseVsEmotivism
