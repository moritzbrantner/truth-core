import TruthCore.Logic.ObjectiveTruthDefinitionFork
import TruthCore.Results.Comparison.ProblemOfEvil.ExternalPremiseVsEmotivism.Solution
namespace TruthCore.Results.Logic.ObjectiveTruthDefinitionFork.ExternalBridge
open TruthCore.Logic.ObjectiveTruthDefinitionFork
open TruthCore.English.OConnor
theorem externalBridge (f : Frame) (SaysBad Moral TruthApt : f.Sentence → Prop)
    (evil : f.Sentence)
    (hEmotivism : MoralStatementsLackTruthValueReading Moral TruthApt)
    (hNoTruth : LackingTruthValueExcludesTruthReading TruthApt (f.holds f.actual))
    (hBadIsMoral : BadnessAscriptionsAreMoralReading SaysBad Moral)
    (hSaysBad : ManMadeEvilPremiseSaysSomethingBadReading SaysBad evil)
    (hTruth : HasTruthComponent f) : ExternalEvilNotObjective f evil := by
  sorry
end TruthCore.Results.Logic.ObjectiveTruthDefinitionFork.ExternalBridge
