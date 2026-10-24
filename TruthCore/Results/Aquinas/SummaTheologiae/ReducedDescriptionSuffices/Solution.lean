import TruthCore.Case.Catholicism.StageOneQuartaVia
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article8
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question4.Article1
namespace TruthCore.Results.Aquinas.SummaTheologiae.ReducedDescriptionSuffices
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism (GodNamesTheUniqueMaximeEns GodNamesTheFullyDescribedPrinciple
  CauseOfBeingCausesEveryPerfection CausesEveryPerfectionOfOthers RemoteFromAll)

/-- Version (b) of the discharge (owner decision on #143, 2026-10-24): a defense
of the reduced nominal definition. The conditions it drops follow from the ones
it keeps. A being that is the only maximum in being and causes the being of all
others also causes every perfection of the others (q.4 a.1 ad 3 and the bridge
supported by q.4 a.2 and q.6 a.2), and it is part of nothing (q.3 a.8). So
whatever meets the reduced description meets the fuller one, and the fuller
definition makes it God. -/
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
  intro m hMax hCauses hOnly
  -- INF-AQUINAS-REDUCED-DESCRIPTION-CAUSES-EVERY-PERFECTION
  have hEvery : CausesEveryPerfectionOfOthers InAct CausesIn m :=
    fun x r hOther hAct => hPerfections m x r (hCauses x hOther (hBeing x r hAct)) hAct
  -- INF-AQUINAS-REDUCED-DESCRIPTION-REMOTE-FROM-ALL
  have hRemote : RemoteFromAll ComponentOf m :=
    fun x hComponent => hNoComponent m x hComponent hMax
  -- INF-AQUINAS-REDUCED-DESCRIPTION-SUFFICES
  exact hFull m hMax hCauses hEvery hRemote hOnly

end TruthCore.Results.Aquinas.SummaTheologiae.ReducedDescriptionSuffices
