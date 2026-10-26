import TruthCore.Results.Aquinas.SummaTheologiae.PrimaVia.Solution
import TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels
namespace TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaFromBeingInAct
open TruthCore.Latin.Aquinas.SummaTheologiae
theorem primaViaFromBeingInAct {Being : Type} {Respect : Type}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (InPotency InAct : Being → Respect → Prop)
    (MovesAsMoved : Being → Being → Prop)
    (hSense : SomethingIsMovedReading MovedIn)
    (hPotency : MovedOnlyAsInPotencyReading MovedIn InPotency)
    (hReduction : ReducedOnlyByABeingInActReading MovedIn MovesIn InAct)
    (hNotBoth : NotActAndPotencyInSameRespectReading InAct InPotency)
    (hPerSe : SecondMoversMoveOnlyAsMovedReading MovedIn MovesIn MovesAsMoved)
    (hRegress : NoInfinitePerSeMoverSeriesReading MovesAsMoved) :
    FirstUnmovedMoverCannotBeLackingReading MovedIn MovesIn := by
  sorry
theorem premisesNeeded : PrimaViaFromBeingInActPremisesNeeded := by
  sorry
end TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaFromBeingInAct
