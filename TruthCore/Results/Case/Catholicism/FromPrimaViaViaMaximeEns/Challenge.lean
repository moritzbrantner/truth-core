import TruthCore.Results.Aquinas.SummaTheologiae.PrimaVia.Solution
import TruthCore.Results.Case.Catholicism.StageOneViaMaximeEns.Solution
import TruthCore.Results.Case.Catholicism.Skeleton.Solution
namespace TruthCore.Results.Case.Catholicism.FromPrimaViaViaMaximeEns
open TruthCore.Case.Catholicism
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Greek.Aristotle.Metaphysics (CauseOfQualityInAnotherIsMoreSuchReading)
open TruthCore.Results.Aquinas.SummaTheologiae.PrimaVia
open TruthCore.Results.Case.Catholicism.StageOneViaMaximeEns
open TruthCore.Results.Case.Catholicism.Skeleton

/-- The root from the *prima via*, with stage 1's uniqueness taken along the
*maxime ens* route (`CATHOLICISM-STAGE1-VIA-MAXIME-ENS`) instead of q.11 a.3.
Composition of three verified results: the *prima via*, stage 1 via *maxime ens*,
and the skeleton. Stages 2–6, the bridges and the gap premises stay open, so like
`CATHOLICISM-FROM-PRIMA-VIA` this is a structural map. -/
theorem catholicismFromPrimaViaViaMaximeEns (σ : Signature) {Respect : Type}
    (MovedIn : σ.Being → Respect → Prop)
    (MovesIn : σ.Being → σ.Being → Respect → Prop)
    (InPotency InAct : σ.Being → Respect → Prop)
    (MovesAsMoved : σ.Being → σ.Being → Prop)
    (MoreIn : Respect → σ.Being → σ.Being → Prop)
    (CausesIn : σ.Being → σ.Being → Respect → Prop)
    (bonum verum nobile esse : Respect)
    (PureAct God : σ.Being → Prop)
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
    (hName : GodNamesTheUniqueMaximeEnsReading InAct MoreIn CausesIn esse God)
    (hApplied : CreatedAgentIsAppliedToActByGodReading MovedIn MovesIn CausesIn esse God)
    (hEM : TruthCore.Logic.ExcludedMiddle)
    (hPureAct : FirstUnmovedMoverIsPureAct MovedIn MovesIn PureAct)
    (hIdentify : UniquePureActFirstMoverIsGod MovedIn MovesIn PureAct σ.IsGod)
    (hAttributes : GodHasClassicalAttributes σ)
    (hRevelation : RevelationPossibleAndRecognizable σ)
    (hJesus : JesusClaimedDivineAuthorityAndRose σ)
    (hFounded : ChristFoundedVisibleChurch σ)
    (hCatholic : ChristsChurchIsCatholicChurch σ)
    (hDivineFounding : BridgeChristsChurchFoundedByGod σ)
    (hOnlyTruth : BridgeGodFoundedAuthorityProposesOnlyTruth σ)
    (hProposes : CatholicChurchDefinitivelyProposesCreed σ) :
    CatholicismTrue σ := by
  sorry

end TruthCore.Results.Case.Catholicism.FromPrimaViaViaMaximeEns
