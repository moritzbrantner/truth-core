import TruthCore.Results.Aquinas.SummaTheologiae.PrimaVia.Solution
import TruthCore.Results.Case.Catholicism.StageOneFromPrimaVia.Solution
import TruthCore.Results.Case.Catholicism.Skeleton.Solution
namespace TruthCore.Results.Case.Catholicism.FromPrimaVia
open TruthCore.Case.Catholicism
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Results.Aquinas.SummaTheologiae.PrimaVia
open TruthCore.Results.Case.Catholicism.StageOneFromPrimaVia
open TruthCore.Results.Case.Catholicism.Skeleton
theorem catholicismFromPrimaVia (σ : Signature) {Respect : Type}
    (MovedIn : σ.Being → Respect → Prop)
    (MovesIn : σ.Being → σ.Being → Respect → Prop)
    (InPotency InAct : σ.Being → Respect → Prop)
    (MovesAsMoved : σ.Being → σ.Being → Prop)
    (PureAct : σ.Being → Prop)
    (hSense : SomethingIsMovedReading MovedIn)
    (hPotency : MovedOnlyAsInPotencyReading MovedIn InPotency)
    (hAct : MovesOnlyAsInActReading MovesIn InAct)
    (hReduction : ReducedOnlyByAMoverReading MovedIn MovesIn)
    (hNotBoth : NotActAndPotencyInSameRespectReading InAct InPotency)
    (hPerSe : SecondMoversMoveOnlyAsMovedReading MovedIn MovesIn MovesAsMoved)
    (hRegress : NoInfinitePerSeMoverSeriesReading MovesAsMoved)
    (hExcludedMiddle : FirstUnmovedMoverExistsOrNot MovedIn MovesIn)
    (hUnique : AtMostOneFirstUnmovedMover MovedIn MovesIn)
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
  -- AQUINAS-ST-I-Q2-A3-PRIMA-VIA: the verified First Way result
  have hFirstWay : FirstUnmovedMoverCannotBeLackingReading MovedIn MovesIn :=
    primaVia MovedIn MovesIn InPotency InAct MovesAsMoved
      hSense hPotency hAct hReduction hNotBoth hPerSe hRegress
  -- CATHOLICISM-STAGE1-FROM-PRIMA-VIA: the verified stage-1 result
  have hGod : GodExists σ.IsGod :=
    stageOneFromPrimaVia MovedIn MovesIn PureAct σ.IsGod
      hFirstWay hExcludedMiddle hUnique hPureAct hIdentify
  -- CATHOLICISM-SKELETON: the verified skeleton result
  exact catholicismSkeleton σ hGod hAttributes hRevelation hJesus hFounded hCatholic
    hDivineFounding hOnlyTruth hProposes
end TruthCore.Results.Case.Catholicism.FromPrimaVia
