import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article1
namespace TruthCore.Results.Aquinas.SummaTheologiae.FirstBeingNoPotency
open TruthCore.Latin.Aquinas.SummaTheologiae
theorem firstBeingNoPotency {Being : Type} {Respect : Type}
    (InPotency InAct : Being → Respect → Prop)
    (PriorSimply : Being → Being → Prop)
    (hPrior : ActSimplyPriorToPotencyReading InAct InPotency PriorSimply)
    (hNotBoth : NotActAndPotencyInSameRespectReading InAct InPotency) :
    FirstBeingIsInNoWayInPotencyReading InPotency PriorSimply := by
  -- INF-AQUINAS-ST-I-Q3-A1-FIRST-BEING-NO-POTENCY
  intro f hFirstBeing r hPot
  -- A potency of f is posterior to some being in act in that respect.
  obtain ⟨y, hYAct, hYPrior⟩ := hPrior f r hPot
  -- Nothing other than the first being is prior to it, so that being is f,
  -- which would then be in act and in potency in the same respect.
  have hEq : y = f := hFirstBeing y hYPrior
  subst hEq
  exact hNotBoth y r ⟨hYAct, hPot⟩
end TruthCore.Results.Aquinas.SummaTheologiae.FirstBeingNoPotency
