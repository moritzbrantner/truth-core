module

public import TruthCore.Logic.ObjectiveTruthDefinitionFork
public import TruthCore.Results.Comparison.ProblemOfEvil.ExternalPremiseVsEmotivism.Solution

@[expose] public section
namespace TruthCore.Results.Logic.ObjectiveTruthDefinitionFork.ExternalBridge
open TruthCore.Logic
open TruthCore.Logic.ObjectiveTruthDefinitionFork
open TruthCore.English.OConnor

theorem externalBridge (f : Frame) (SaysBad Moral TruthApt : f.Sentence → Prop)
    (evil : f.Sentence)
    (hEmotivism : MoralStatementsLackTruthValueReading Moral TruthApt)
    (hNoTruth : LackingTruthValueExcludesTruthReading TruthApt (f.holds f.actual))
    (hBadIsMoral : BadnessAscriptionsAreMoralReading SaysBad Moral)
    (hSaysBad : ManMadeEvilPremiseSaysSomethingBadReading SaysBad evil)
    (hTruth : HasTruthComponent f) : ExternalEvilNotObjective f evil := by
  have hNotTrue := TruthCore.Results.Comparison.ProblemOfEvil.ExternalPremiseVsEmotivism.externalPremiseContradictsEmotivism
    SaysBad Moral TruthApt (f.holds f.actual) evil hEmotivism hNoTruth hBadIsMoral hSaysBad
  intro hObjective
  exact hNotTrue (hTruth evil hObjective)

end TruthCore.Results.Logic.ObjectiveTruthDefinitionFork.ExternalBridge
