import TruthCore.Results.Aquinas.SummaTheologiae.AtMostOneMaximeEns.Solution
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article8
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question4.Article1
namespace TruthCore.Results.Aquinas.SummaTheologiae.MaximeEnsIsGodViaFullDescriptionIdentity
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Greek.Aristotle.Metaphysics (CauseOfQualityInAnotherIsMoreSuchReading)
open TruthCore.Case.Catholicism (MaximumInBeingIsFirstBeing MaximeEnsIsGod AtMostOneMaximeEns GodNamesTheFullyDescribedPrinciple
  CauseOfBeingCausesEveryPerfection CausesEveryPerfectionOfOthers RemoteFromAll)

/-- Separate sufficient equality-decision interface. All nonlogical premises remain open.
No existence follows from naming or identifying supplied witnesses. No necessity,
minimality, strict-strength or philosophical-discharge claim. The historical
end, where present, retains the existing structural transcription. -/
theorem maximeEnsIsGodViaFullDescription {Being : Type} {Respect : Type}
    [DecidableEq Being]
    (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (ComponentOf PriorSimply : Being → Being → Prop) (God : Being → Prop)
    (hGenus : MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn)
    (hCauseMore : CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn)
    (hBeing : ActualityOnlyInsofarAsBeingReading InAct esse)
    (hPerfections : CauseOfBeingCausesEveryPerfection InAct CausesIn esse)
    (hNoComponent : NoComponentIsFirstBeingReading ComponentOf PriorSimply)
    (hFirstBeing : MaximumInBeingIsFirstBeing InAct MoreIn esse PriorSimply)
    (hFull : GodNamesTheFullyDescribedPrinciple InAct MoreIn CausesIn esse ComponentOf God) :
    MaximeEnsIsGod InAct MoreIn esse God := by
  intro m hMax
  -- INF-AQUINAS-FULL-DESCRIPTION-CAUSE-OF-BEING: the genus principle at esse
  have hCauses : CausesAllInGenus InAct CausesIn esse m := hGenus esse m hMax
  -- INF-AQUINAS-AT-MOST-ONE-MAXIME-ENS (result AQUINAS-ST-I-Q2-A3-AT-MOST-ONE-MAXIME-ENS)
  have hUnique : AtMostOneMaximeEns InAct MoreIn esse :=
    by
      intro a b ha hb
      by_cases hSame : a = b
      · exact hSame
      · exact (hb.2 a (hCauseMore a b esse hSame
          (hGenus esse a ha b (fun h => hSame h.symm) hb.1))).elim
  -- INF-AQUINAS-MAXIME-ENS-CAUSES-EVERY-PERFECTION
  have hEvery : CausesEveryPerfectionOfOthers InAct CausesIn m :=
    fun x r hOther hAct => hPerfections m x r (hCauses x hOther (hBeing x r hAct)) hAct
  -- INF-AQUINAS-MAXIME-ENS-REMOTE-FROM-ALL
  have hRemote : RemoteFromAll ComponentOf m :=
    fun x hComponent => hNoComponent m x hComponent (hFirstBeing m hMax)
  -- INF-AQUINAS-MAXIME-ENS-IS-GOD-VIA-FULL-DESCRIPTION
  exact hFull m hMax hCauses hEvery hRemote (fun m' hMax' => hUnique m' m hMax' hMax)


end TruthCore.Results.Aquinas.SummaTheologiae.MaximeEnsIsGodViaFullDescriptionIdentity
