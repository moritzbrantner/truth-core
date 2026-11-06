import TruthCore.Metaethics.EvilObjection

namespace TruthCore.Results.Metaethics.EvilObjection.UseFork

open TruthCore.Metaethics.EvilObjection TruthCore.English.OConnor TruthCore.English.Rowe TruthCore.Logic

theorem emotivistUseFork (c : Critic) (s : Sig)
    (hEM : ExcludedMiddle)
    (hEmotivism : MoralStatementsLackTruthValueReading c.Moral c.TruthApt)
    (hNoTruth : LackingTruthValueExcludesTruthReading c.TruthApt c.Holds)
    (hBadIsMoral : BadnessAscriptionsAreMoralReading c.SaysBad c.Moral)
    (hSaysBad : ManMadeEvilPremiseSaysSomethingBadReading c.SaysBad c.evilUtterance) :
    EmotivistUseFork c s := by
  sorry

end TruthCore.Results.Metaethics.EvilObjection.UseFork
