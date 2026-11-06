import TruthCore.Results.Case.Catholicism.FromPrimaVia.Solution
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.AdoptedPotency
namespace TruthCore.Results.Case.Catholicism.AdoptedPotency.FromPrimaVia
open TruthCore.Case.Catholicism
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- Adopted-potency specialization of `CATHOLICISM-FROM-PRIMA-VIA`. Every occurrence of the old
potency parameter, including immutability, priority and sufficiency, is uniformly
`CanBe x r ∧ ¬ InAct x r`. The generic frozen Challenge is retained. F1 supplies
non-overlap; all other original hypotheses retain their existing scope. -/
theorem catholicismFromPrimaVia (σ : Signature)
    {Respect : Type}
    (MovedIn : σ.Being → Respect → Prop)
    (MovesIn : σ.Being → σ.Being → Respect → Prop)
    (CanBe InAct : σ.Being → Respect → Prop)
    (MovesAsMoved : σ.Being → σ.Being → Prop)
    (PureAct : σ.Being → Prop)
    (hSense : SomethingIsMovedReading MovedIn)
    (hPotency : MovedOnlyAsInPotencyReading MovedIn (TruthCore.Latin.Aquinas.SummaTheologiae.AdoptedPotency.InPotency InAct CanBe))
    (hAct : MovesOnlyAsInActReading MovesIn InAct)
    (hReduction : ReducedOnlyByAMoverReading MovedIn MovesIn)
    (hF1 : TruthCore.Logic.CaseNonContradiction.CasePredicateNonContradiction.{1, 1})
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
    (hProposes : CatholicChurchDefinitivelyProposesCreed σ):
    CatholicismTrue σ := by
  sorry
end TruthCore.Results.Case.Catholicism.AdoptedPotency.FromPrimaVia
