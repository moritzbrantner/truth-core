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
  -- INF-EVIL-PREMISE-IS-MORAL: the man-made-evil premise says something is bad, so it is moral.
  have hMoral : Moral moralEvilPremise := hBadIsMoral moralEvilPremise hSaysBad
  -- INF-EMOTIVISM-EVIL-PREMISE-NOT-TRUTH-APT
  have hNotApt : ¬ TruthApt moralEvilPremise := hEmotivism moralEvilPremise hMoral
  -- INF-EMOTIVISM-EXCLUDES-EXTERNAL-EVIL-PREMISE
  exact hNoTruth moralEvilPremise hNotApt
end TruthCore.Results.Comparison.ProblemOfEvil.ExternalPremiseVsEmotivism
