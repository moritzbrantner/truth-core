import TruthCore.Results.Aquinas.SummaTheologiae.AtMostOneMaximeEns.Solution
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article8
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question4.Article1
namespace TruthCore.Results.Aquinas.SummaTheologiae.MaximeEnsIsGodViaFullDescription
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Greek.Aristotle.Metaphysics (CauseOfQualityInAnotherIsMoreSuchReading)
open TruthCore.Case.Catholicism (MaximeEnsIsGod AtMostOneMaximeEns GodNamesTheFullyDescribedPrinciple
  CauseOfBeingCausesEveryPerfection CausesEveryPerfectionOfOthers RemoteFromAll)
theorem maximeEnsIsGodViaFullDescription {Being : Type} {Respect : Type}
    (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (ComponentOf : Being → Being → Prop) (God : Being → Prop)
    (hGenus : MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn)
    (hCauseMore : CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn)
    (hEM : TruthCore.Logic.ExcludedMiddle)
    (hBeing : ActualityOnlyInsofarAsBeingReading InAct esse)
    (hPerfections : CauseOfBeingCausesEveryPerfection InAct CausesIn esse)
    (hNoComponent : NoComponentIsMaximalInBeingReading InAct MoreIn esse ComponentOf)
    (hFull : GodNamesTheFullyDescribedPrinciple InAct MoreIn CausesIn esse ComponentOf God) :
    MaximeEnsIsGod InAct MoreIn esse God := by
  sorry
end TruthCore.Results.Aquinas.SummaTheologiae.MaximeEnsIsGodViaFullDescription
