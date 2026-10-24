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
  sorry
end TruthCore.Results.Case.Catholicism.StageTwo.GodIsSupremelyGood
