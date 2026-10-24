import TruthCore.Case.Catholicism.StageOneQuartaVia
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article8
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question4.Article1
namespace TruthCore.Results.Aquinas.SummaTheologiae.ReducedDescriptionSuffices
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism (GodNamesTheUniqueMaximeEns GodNamesTheFullyDescribedPrinciple
  CauseOfBeingCausesEveryPerfection CausesEveryPerfectionOfOthers RemoteFromAll)
theorem reducedDescriptionSuffices {Being : Type} {Respect : Type}
    (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (ComponentOf : Being → Being → Prop) (God : Being → Prop)
    (hBeing : ActualityOnlyInsofarAsBeingReading InAct esse)
    (hPerfections : CauseOfBeingCausesEveryPerfection InAct CausesIn esse)
    (hNoComponent : NoComponentIsMaximalInBeingReading InAct MoreIn esse ComponentOf)
    (hFull : GodNamesTheFullyDescribedPrinciple InAct MoreIn CausesIn esse ComponentOf God) :
    GodNamesTheUniqueMaximeEns InAct MoreIn CausesIn esse God := by
  sorry
end TruthCore.Results.Aquinas.SummaTheologiae.ReducedDescriptionSuffices
