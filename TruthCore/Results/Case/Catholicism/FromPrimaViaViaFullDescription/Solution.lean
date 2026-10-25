import TruthCore.Results.Aquinas.SummaTheologiae.PrimaVia.Solution
import TruthCore.Results.Case.Catholicism.StageOneViaFullDescription.Solution
import TruthCore.Results.Case.Catholicism.Skeleton.Solution
namespace TruthCore.Results.Case.Catholicism.FromPrimaViaViaFullDescription
open TruthCore.Case.Catholicism
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Greek.Aristotle.Metaphysics (CauseOfQualityInAnotherIsMoreSuchReading)
open TruthCore.Results.Aquinas.SummaTheologiae.PrimaVia
open TruthCore.Results.Case.Catholicism.StageOneViaFullDescription
open TruthCore.Results.Case.Catholicism.Skeleton

/-- The root from the *prima via*, with stage 1 taken along the fuller nominal
definition (`CATHOLICISM-STAGE1-VIA-FULL-DESCRIPTION`): the skeleton's `IsGod` is
the predicate that definition applies. Composition of three verified results:
the *prima via*, stage 1 via the full description, and the skeleton. This is the
designated root route (`root_route`, owner decision on #143, 2026-10-24). Stages
2–6 and the bridges stay open, so like the other root compositions this is a
structural map. -/
theorem catholicismFromPrimaViaViaFullDescription (σ : Signature) {Respect : Type}
    (MovedIn : σ.Being → Respect → Prop)
    (MovesIn : σ.Being → σ.Being → Respect → Prop)
    (InPotency InAct : σ.Being → Respect → Prop)
    (MovesAsMoved : σ.Being → σ.Being → Prop)
    (MoreIn : Respect → σ.Being → σ.Being → Prop)
    (CausesIn : σ.Being → σ.Being → Respect → Prop)
    (bonum verum nobile esse : Respect)
    (ComponentOf PriorSimply : σ.Being → σ.Being → Prop)
    (hSense : SomethingIsMovedReading MovedIn)
    (hPotency : MovedOnlyAsInPotencyReading MovedIn InPotency)
    (hAct : MovesOnlyAsInActReading MovesIn InAct)
    (hReduction : ReducedOnlyByAMoverReading MovedIn MovesIn)
    (hNotBoth : NotActAndPotencyInSameRespectReading InAct InPotency)
    (hPerSe : SecondMoversMoveOnlyAsMovedReading MovedIn MovesIn MovesAsMoved)
    (hRegress : NoInfinitePerSeMoverSeriesReading MovesAsMoved)
    (hExcludedMiddle : FirstUnmovedMoverExistsOrNot MovedIn MovesIn)
    (hGrades : GradesFoundInThingsReading MoreIn bonum verum nobile)
    (hApproach : GradesByApproachToAMaximumReading InAct MoreIn)
    (hTrue : MostTrueIsMostBeingReading InAct MoreIn verum esse)
    (hGenus : MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn)
    (hBeing : ActualityOnlyInsofarAsBeingReading InAct esse)
    (hCauseMore : CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn)
    (hEM : TruthCore.Logic.ExcludedMiddle)
    (hPerfections : CauseOfBeingCausesEveryPerfection InAct CausesIn esse)
    (hNoComponent : NoComponentIsFirstBeingReading ComponentOf PriorSimply)
    (hFirstBeing : MaximumInBeingIsFirstBeing InAct MoreIn esse PriorSimply)
    (hFull : GodNamesTheFullyDescribedPrinciple InAct MoreIn CausesIn esse ComponentOf σ.IsGod)
    (hApplied : CreatedAgentIsAppliedToActByGodReading MovedIn MovesIn CausesIn esse σ.IsGod)
    (hAttributes : GodHasClassicalAttributes σ)
    (hRevelation : RevelationPossibleAndRecognizable σ)
    (hJesus : JesusClaimedDivineAuthorityAndRose σ)
    (hFounded : ChristFoundedVisibleChurch σ)
    (hCatholic : ChristsChurchIsCatholicChurch σ)
    (hDivineFounding : BridgeChristsChurchFoundedByGod σ)
    (hOnlyTruth : BridgeGodFoundedAuthorityProposesOnlyTruth σ)
    (hProposes : CatholicChurchDefinitivelyProposesCreed σ) :
    CatholicismTrue σ := by
  -- AQUINAS-ST-I-Q2-A3-PRIMA-VIA: the verified First Way result
  have hFirstWay : FirstUnmovedMoverCannotBeLackingReading MovedIn MovesIn :=
    primaVia MovedIn MovesIn InPotency InAct MovesAsMoved
      hSense hPotency hAct hReduction hNotBoth hPerSe hRegress
  -- CATHOLICISM-STAGE1-VIA-FULL-DESCRIPTION: the verified stage-1 result
  have hGod : GodExists σ.IsGod :=
    stageOneViaFullDescription MovedIn MovesIn InAct MoreIn CausesIn bonum verum nobile esse
      ComponentOf PriorSimply σ.IsGod hFirstWay hExcludedMiddle hGrades hApproach hTrue hGenus hAct hBeing
      hCauseMore hEM hPerfections hNoComponent hFirstBeing hFull hApplied
  -- CATHOLICISM-SKELETON: the verified skeleton result
  exact catholicismSkeleton σ hGod hAttributes hRevelation hJesus hFounded hCatholic
    hDivineFounding hOnlyTruth hProposes

end TruthCore.Results.Case.Catholicism.FromPrimaViaViaFullDescription
