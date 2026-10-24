import TruthCore.Case.Catholicism.StageOneConvergence
import TruthCore.Results.Aquinas.SummaTheologiae.QuintaViaOneGovernor.Solution
import TruthCore.Results.Aquinas.SummaTheologiae.QuartaVia.Solution
import TruthCore.Results.Aquinas.SummaTheologiae.FirstMoverIsMaximeEns.Solution
import TruthCore.Results.Aquinas.SummaTheologiae.MaximeEnsIsGod.Solution
namespace TruthCore.Results.Aquinas.SummaTheologiae.QuintaViaGovernorIsMaximeEns
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Greek.Aristotle.Metaphysics (CauseOfQualityInAnotherIsMoreSuchReading)
open TruthCore.Case.Catholicism (AtMostOneFirstUnmovedMover NaturalDirectionReducedToIntelligentImmobileDirector
  DirectingIsMoving GodNamesTheUniqueMaximeEns MaximeEnsGovernsNature)

/-- The *quinta via* converges on the *quarta via*. One intelligent first mover
moved by none governs nature (`AQUINAS-ST-I-Q2-A3-QUINTA-VIA-ONE-GOVERNOR`).
Something is maximal in being (`AQUINAS-ST-I-Q2-A3-QUARTA-VIA`), and every first
mover moved by none is that maximum (`AQUINAS-ST-I-Q2-A3-FIRST-MOVER-IS-MAXIME-ENS`,
with `AQUINAS-ST-I-Q2-A3-MAXIME-ENS-IS-GOD`). So the governor of nature is the
maximal being. A composition of verified results. -/
theorem governorIsMaximeEns {Being : Type} {Respect : Type} {End : Type}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop)
    (bonum verum nobile esse : Respect)
    (NaturalBody HasCognition Intelligent God : Being → Prop)
    (RegularlyAttains Best ByChance TendsTo : Being → End → Prop)
    (Directs : Being → Being → End → Prop)
    (hLack : NaturalBodiesLackCognitionReading NaturalBody HasCognition)
    (hObs : NaturalBodiesActRegularlyForTheBestReading NaturalBody RegularlyAttains Best)
    (hNotChance : RegularityIsNotByChanceReading RegularlyAttains ByChance)
    (hDich : RegularBestByChanceOrByIntentionReading RegularlyAttains Best ByChance TendsTo)
    (hArrow : NonCognitiveTendingNeedsKnowingDirectorReading HasCognition Intelligent
      TendsTo Directs)
    (hReduce : NaturalDirectionReducedToIntelligentImmobileDirector MovedIn NaturalBody
      HasCognition Intelligent Directs)
    (hMoving : DirectingIsMoving MovesIn Directs)
    (hOne : AtMostOneFirstUnmovedMover MovedIn MovesIn)
    (hGrades : GradesFoundInThingsReading MoreIn bonum verum nobile)
    (hApproach : GradesByApproachToAMaximumReading InAct MoreIn)
    (hTrue : MostTrueIsMostBeingReading InAct MoreIn verum esse)
    (hGenus : MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn)
    (hInAct : MovesOnlyAsInActReading MovesIn InAct)
    (hBeing : ActualityOnlyInsofarAsBeingReading InAct esse)
    (hCauseMore : CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn)
    (hEM : TruthCore.Logic.ExcludedMiddle)
    (hName : GodNamesTheUniqueMaximeEns InAct MoreIn CausesIn esse God)
    (hApplied : CreatedAgentIsAppliedToActByGodReading MovedIn MovesIn CausesIn esse God) :
    MaximeEnsGovernsNature InAct MoreIn esse NaturalBody Intelligent Directs := by
  -- AQUINAS-ST-I-Q2-A3-QUINTA-VIA-ONE-GOVERNOR
  obtain ⟨d, hFirst, hIntelligent, hGoverns⟩ :=
    QuintaViaOneGovernor.oneGovernor MovedIn MovesIn NaturalBody HasCognition Intelligent
      RegularlyAttains Best ByChance TendsTo Directs hLack hObs hNotChance hDich hArrow
      hReduce hMoving hOne
  -- AQUINAS-ST-I-Q2-A3-QUARTA-VIA
  obtain ⟨m, hMax, _⟩ := QuartaVia.quartaVia InAct MoreIn CausesIn bonum verum nobile esse
    hGrades hApproach hTrue hGenus
  -- AQUINAS-ST-I-Q2-A3-MAXIME-ENS-IS-GOD and -FIRST-MOVER-IS-MAXIME-ENS
  have hGod := MaximeEnsIsGod.maximeEnsIsGod InAct MoreIn CausesIn esse God hGenus hCauseMore
    hEM hName
  have hSame : d = m :=
    FirstMoverIsMaximeEns.firstMoverIsMaximeEns MovedIn MovesIn InAct MoreIn CausesIn esse God
      hGenus hInAct hBeing hGod hApplied hEM d hFirst m hMax
  -- INF-QUINTA-VIA-GOVERNOR-IS-MAXIME-ENS
  exact ⟨m, hMax, hSame ▸ hIntelligent, hSame ▸ hGoverns⟩

end TruthCore.Results.Aquinas.SummaTheologiae.QuintaViaGovernorIsMaximeEns
