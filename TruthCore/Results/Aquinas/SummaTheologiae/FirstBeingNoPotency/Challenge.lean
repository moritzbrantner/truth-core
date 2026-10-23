import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article1
namespace TruthCore.Results.Aquinas.SummaTheologiae.FirstBeingNoPotency
open TruthCore.Latin.Aquinas.SummaTheologiae
theorem firstBeingNoPotency {Being : Type} {Respect : Type}
    (InPotency InAct : Being → Respect → Prop)
    (PriorSimply : Being → Being → Prop)
    (hPrior : ActSimplyPriorToPotencyReading InAct InPotency PriorSimply)
    (hNotBoth : NotActAndPotencyInSameRespectReading InAct InPotency) :
    FirstBeingIsInNoWayInPotencyReading InPotency PriorSimply := by
  sorry
end TruthCore.Results.Aquinas.SummaTheologiae.FirstBeingNoPotency
