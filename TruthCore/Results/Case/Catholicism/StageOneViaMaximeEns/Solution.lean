import TruthCore.Results.Case.Catholicism.StageOneFromPrimaVia.Solution
import TruthCore.Results.Aquinas.SummaTheologiae.OneFirstMoverViaMaximeEns.Solution
import TruthCore.Results.Aquinas.SummaTheologiae.MaximeEnsIsGod.Solution
namespace TruthCore.Results.Case.Catholicism.StageOneViaMaximeEns
open TruthCore.Case.Catholicism
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Greek.Aristotle.Metaphysics (CauseOfQualityInAnotherIsMoreSuchReading)
open TruthCore.Results.Case.Catholicism.StageOneFromPrimaVia
open TruthCore.Results.Aquinas.SummaTheologiae.OneFirstMoverViaMaximeEns
open TruthCore.Results.Aquinas.SummaTheologiae.MaximeEnsIsGod

/-- Stage 1 with its uniqueness step taken along the *maxime ens* route (#143,
2026-10-24). The first mover moved by none is unique because every such mover is
the *quarta via*'s maximal being (`AQUINAS-ST-I-Q2-A3-ONE-FIRST-MOVER-VIA-MAXIME-ENS`),
and the maximal being is God by the uniqueness of the maximum and the nominal
definition (`AQUINAS-ST-I-Q2-A3-MAXIME-ENS-IS-GOD`). The every-perfection bridge
and the plural-difference premise of q.11 a.3 are not used. The rest is
`CATHOLICISM-STAGE1-FROM-PRIMA-VIA`, applied unchanged.

`God` is the one the *Summa* calls God (q.105 a.5, q.13 a.8); `IsGod` is the
skeleton's predicate. They stay separate parameters: identifying them is the open
premise `UniquePureActFirstMoverIsGod`, as before. -/
theorem stageOneViaMaximeEns {Being : Type} {Respect : Type}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop)
    (bonum verum nobile esse : Respect)
    (PureAct IsGod God : Being → Prop)
    (hFirstWay : FirstUnmovedMoverCannotBeLackingReading MovedIn MovesIn)
    (hExcludedMiddle : FirstUnmovedMoverExistsOrNot MovedIn MovesIn)
    (hGrades : GradesFoundInThingsReading MoreIn bonum verum nobile)
    (hApproach : GradesByApproachToAMaximumReading InAct MoreIn)
    (hTrue : MostTrueIsMostBeingReading InAct MoreIn verum esse)
    (hGenus : MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn)
    (hInAct : MovesOnlyAsInActReading MovesIn InAct)
    (hBeing : ActualityOnlyInsofarAsBeingReading InAct esse)
    (hCauseMore : CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn)
    (hName : GodNamesTheUniqueMaximeEns InAct MoreIn CausesIn esse God)
    (hApplied : CreatedAgentIsAppliedToActByGodReading MovedIn MovesIn CausesIn esse God)
    (hEM : TruthCore.Logic.ExcludedMiddle)
    (hPureAct : FirstUnmovedMoverIsPureAct MovedIn MovesIn PureAct)
    (hIdentify : UniquePureActFirstMoverIsGod MovedIn MovesIn PureAct IsGod) :
    GodExists IsGod := by
  -- AQUINAS-ST-I-Q2-A3-MAXIME-ENS-IS-GOD: the maximal being is God
  have hGod : MaximeEnsIsGod InAct MoreIn esse God :=
    maximeEnsIsGod InAct MoreIn CausesIn esse God hGenus hCauseMore hEM hName
  -- AQUINAS-ST-I-Q2-A3-ONE-FIRST-MOVER-VIA-MAXIME-ENS: uniqueness of the first mover
  have hUnique : AtMostOneFirstUnmovedMover MovedIn MovesIn :=
    oneFirstMoverViaMaximeEns MovedIn MovesIn InAct MoreIn CausesIn bonum verum nobile
      esse God hGrades hApproach hTrue hGenus hInAct hBeing hGod hApplied hEM
  -- CATHOLICISM-STAGE1-FROM-PRIMA-VIA
  exact stageOneFromPrimaVia MovedIn MovesIn PureAct IsGod hFirstWay hExcludedMiddle
    hUnique hPureAct hIdentify
end TruthCore.Results.Case.Catholicism.StageOneViaMaximeEns
