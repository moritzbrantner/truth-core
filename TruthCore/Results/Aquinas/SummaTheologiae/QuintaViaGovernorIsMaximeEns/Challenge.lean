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
  sorry
end TruthCore.Results.Aquinas.SummaTheologiae.QuintaViaGovernorIsMaximeEns
