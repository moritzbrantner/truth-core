import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3
namespace TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaRelative
open TruthCore.Latin.Aquinas.SummaTheologiae
theorem primaViaRelative {Being : Type} {Respect : Type}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (InPotency InAct : Being → Respect → Prop)
    (MovesAsMoved : Being → Being → Prop)
    (RelevantTo : Being → Being → Respect → Respect → Prop)
    (hSense : SomethingIsMovedReading MovedIn)
    (hPotency : MovedOnlyAsInPotencyReading MovedIn InPotency)
    (hAct : MovesOnlyAsInActReading MovesIn InAct)
    (hReduction : ReducedOnlyByAMoverReading MovedIn MovesIn)
    (hNotBoth : NotActAndPotencyInSameRespectReading InAct InPotency)
    (hPerSe : SecondMoversMoveAsMovedInRelevantRespectReading
      MovedIn MovesIn MovesAsMoved RelevantTo)
    (hRegress : NoInfinitePerSeMoverSeriesReading MovesAsMoved) :
    RelativelyUnmovedMoverCannotBeLackingReading MovedIn MovesIn RelevantTo := by
  sorry
end TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaRelative
