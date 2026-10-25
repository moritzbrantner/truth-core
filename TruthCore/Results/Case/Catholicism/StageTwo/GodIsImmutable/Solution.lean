import TruthCore.Results.Aquinas.SummaTheologiae.FirstBeingNoPotency.Solution
import TruthCore.Case.Catholicism.StageTwo
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article1
namespace TruthCore.Results.Case.Catholicism.StageTwo.GodIsImmutable
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism

/-- God is altogether immutable (ST I q.9 a.1, first reason): the first being is
pure act, and whatever is changed in any way is in some way in potency. Whatever
is God is maximal in being, so the first being (open bridge
`MaximumInBeingIsFirstBeing`, #194), and the first being is in potency in no
respect (q.3 a.1). -/
theorem godIsImmutable {Being : Type} {Respect : Type}
    (IsGod : Being → Prop) (InPotency InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop) (esse : Respect)
    (PriorSimply : Being → Being → Prop)
    (hMaximal : GodIsMaximalInBeing IsGod InAct MoreIn esse)
    (hFirstBeing : MaximumInBeingIsFirstBeing InAct MoreIn esse PriorSimply)
    (hPrior : ActSimplyPriorToPotencyReading InAct InPotency PriorSimply)
    (hNotBoth : NotActAndPotencyInSameRespectReading InAct InPotency) :
    GodIsImmutable IsGod (IsImmutable InPotency) := by
  -- INF-STAGE2-GOD-IS-IMMUTABLE
  intro g hg
  -- AQUINAS-ST-I-Q3-A1-FIRST-BEING-NO-POTENCY (imported): the first being is in
  -- potency in no respect, from act's simple priority and q.2 a.3's act/potency rule.
  have hPureAct := TruthCore.Results.Aquinas.SummaTheologiae.FirstBeingNoPotency.firstBeingNoPotency
    InPotency InAct PriorSimply hPrior hNotBoth
  exact hPureAct g (hFirstBeing g (hMaximal g hg))

end TruthCore.Results.Case.Catholicism.StageTwo.GodIsImmutable
