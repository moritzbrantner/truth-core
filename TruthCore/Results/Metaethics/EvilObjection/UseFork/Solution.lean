module

public import TruthCore.Metaethics.EvilObjection
public import TruthCore.Results.Metaethics.EvilObjection.Coverage.Solution
public import TruthCore.Results.Comparison.ProblemOfEvil.ExternalPremiseVsEmotivism.Solution

@[expose] public section

namespace TruthCore.Results.Metaethics.EvilObjection.UseFork

open TruthCore.Metaethics.EvilObjection TruthCore.English.OConnor TruthCore.English.Rowe TruthCore.Logic

theorem emotivistUseFork (c : Critic) (s : Sig)
    (hEM : ExcludedMiddle)
    (hEmotivism : MoralStatementsLackTruthValueReading c.Moral c.TruthApt)
    (hNoTruth : LackingTruthValueExcludesTruthReading c.TruthApt c.Holds)
    (hBadIsMoral : BadnessAscriptionsAreMoralReading c.SaysBad c.Moral)
    (hSaysBad : ManMadeEvilPremiseSaysSomethingBadReading c.SaysBad c.evilUtterance) :
    EmotivistUseFork c s := by
  have hNot : ¬ OwnTruePremise c :=
    TruthCore.Results.Comparison.ProblemOfEvil.ExternalPremiseVsEmotivism.externalPremiseContradictsEmotivism
      c.SaysBad c.Moral c.TruthApt c.Holds c.evilUtterance
      hEmotivism hNoTruth hBadIsMoral hSaysBad
  refine ⟨hNot, ?_⟩
  cases Coverage.useCoverageWithRemainder c s hEM with
  | inl h => exact False.elim (hNot h)
  | inr h => exact h

end TruthCore.Results.Metaethics.EvilObjection.UseFork
