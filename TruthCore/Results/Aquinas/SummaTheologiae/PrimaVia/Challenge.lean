import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3
namespace TruthCore.Results.Aquinas.SummaTheologiae.PrimaVia
open TruthCore.Latin.Aquinas.SummaTheologiae
theorem primaVia {Being : Type} {Respect : Type}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (InPotency InAct : Being → Respect → Prop)
    (MovesAsMoved : Being → Being → Prop)
    (hSense : SomethingIsMovedReading MovedIn)
    (hPotency : MovedOnlyAsInPotencyReading MovedIn InPotency)
    (hAct : MovesOnlyAsInActReading MovesIn InAct)
    (hReduction : ReducedOnlyByAMoverReading MovedIn MovesIn)
    (hNotBoth : NotActAndPotencyInSameRespectReading InAct InPotency)
    (hPerSe : SecondMoversMoveOnlyAsMovedReading MovedIn MovesIn MovesAsMoved)
    (hRegress : NoInfinitePerSeMoverSeriesReading MovesAsMoved) :
    FirstUnmovedMoverCannotBeLackingReading MovedIn MovesIn := by
  sorry
end TruthCore.Results.Aquinas.SummaTheologiae.PrimaVia
