import TruthCore.Metaethics.EvilObjection

namespace TruthCore.Results.Metaethics.EvilObjection.NamedElimination

open TruthCore.Metaethics.EvilObjection TruthCore.English.OConnor TruthCore.English.Rowe TruthCore.Logic

theorem namedEmotivistAlternatives (c : Critic) (s : Sig)
    (hCoverage : NamedUseCoverage c s)
    (hEmotivism : MoralStatementsLackTruthValueReading c.Moral c.TruthApt)
    (hNoTruth : LackingTruthValueExcludesTruthReading c.TruthApt c.Holds)
    (hBadIsMoral : BadnessAscriptionsAreMoralReading c.SaysBad c.Moral)
    (hSaysBad : ManMadeEvilPremiseSaysSomethingBadReading c.SaysBad c.evilUtterance) :
    NamedEmotivistAlternatives c s := by
  sorry

end TruthCore.Results.Metaethics.EvilObjection.NamedElimination
