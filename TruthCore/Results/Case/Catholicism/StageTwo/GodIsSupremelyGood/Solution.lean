import TruthCore.Case.Catholicism.StageTwo
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question4.Article1
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question5.Article1
namespace TruthCore.Results.Case.Catholicism.StageTwo.GodIsSupremelyGood
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism

theorem godIsSupremelyGood {Being : Type} {Respect : Type}
    (IsGod : Being → Prop) (InAct GoodIn : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (hMaximal : GodIsMaximalInBeing IsGod InAct MoreIn esse)
    (hGenus : MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn)
    (hBeing : ActualityOnlyInsofarAsBeingReading InAct esse)
    (hGoodness : GoodnessIsActualityReading GoodIn InAct)
    (hPerfections : CauseOfBeingCausesEveryPerfection InAct CausesIn esse) :
    GodIsSupremelyGood IsGod InAct GoodIn CausesIn esse := by
  intro g hg
  have hMax := hMaximal g hg
  -- INF-STAGE2-GOD-IS-GOOD-IN-BEING: God is in act as to being, so good in it (q.5 a.1)
  refine ⟨(hGoodness g esse).mpr hMax.1, ?_⟩
  -- INF-STAGE2-GOD-CAUSES-EVERY-PERFECTION: as in version (a) of stage 1 (q.6 a.2)
  intro x r hOther hx
  exact hPerfections g x r (hGenus esse g hMax x hOther (hBeing x r hx)) hx

end TruthCore.Results.Case.Catholicism.StageTwo.GodIsSupremelyGood
