module

public import TruthCore.Results.Case.Catholicism.FromPrimaViaViaMaximeEns.Solution
public import TruthCore.Results.Aquinas.SummaTheologiae.AdoptedPotencyNonOverlap.Solution

@[expose] public section

namespace TruthCore.Results.Case.Catholicism.AdoptedPotency.FromPrimaViaViaMaximeEns
open TruthCore.Case.Catholicism
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Greek.Aristotle.Metaphysics (CauseOfQualityInAnotherIsMoreSuchReading)
open TruthCore.Results.Aquinas.SummaTheologiae.PrimaVia
open TruthCore.Results.Case.Catholicism.StageOneViaMaximeEns
open TruthCore.Results.Case.Catholicism.Skeleton

/-- Adopted-potency specialization of `CATHOLICISM-FROM-PRIMA-VIA-VIA-MAXIME-ENS`. Every occurrence of the old
potency parameter, including immutability, priority and sufficiency, is uniformly
`CanBe x r ∧ ¬ InAct x r`. The generic frozen Challenge is retained. F1 supplies
non-overlap; all other original hypotheses retain their existing scope. -/
theorem catholicismFromPrimaViaViaMaximeEns (σ : Signature)
    {Respect : Type}
    (MovedIn : σ.Being → Respect → Prop)
    (MovesIn : σ.Being → σ.Being → Respect → Prop)
    (CanBe InAct : σ.Being → Respect → Prop)
    (MovesAsMoved : σ.Being → σ.Being → Prop)
    (MoreIn : Respect → σ.Being → σ.Being → Prop)
    (CausesIn : σ.Being → σ.Being → Respect → Prop)
    (bonum verum nobile esse : Respect)
    (PureAct God : σ.Being → Prop)
    (hSense : SomethingIsMovedReading MovedIn)
    (hPotency : MovedOnlyAsInPotencyReading MovedIn (TruthCore.Latin.Aquinas.SummaTheologiae.AdoptedPotency.InPotency InAct CanBe))
    (hAct : MovesOnlyAsInActReading MovesIn InAct)
    (hReduction : ReducedOnlyByAMoverReading MovedIn MovesIn)
    (hF1 : TruthCore.Logic.CaseNonContradiction.CasePredicateNonContradiction.{1, 1})
    (hPerSe : SecondMoversMoveOnlyAsMovedReading MovedIn MovesIn MovesAsMoved)
    (hRegress : NoInfinitePerSeMoverSeriesReading MovesAsMoved)
    (hExcludedMiddle : FirstUnmovedMoverExistsOrNot MovedIn MovesIn)
    (hGrades : GradesFoundInThingsReading MoreIn bonum verum nobile)
    (hApproach : GradesByApproachToAMaximumReading InAct MoreIn)
    (hTrue : MostTrueIsMostBeingReading InAct MoreIn verum esse)
    (hGenus : MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn)
    (hBeing : ActualityOnlyInsofarAsBeingReading InAct esse)
    (hCauseMore : CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn)
    (hName : GodNamesTheUniqueMaximeEns InAct MoreIn CausesIn esse God)
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
    (hProposes : CatholicChurchDefinitivelyProposesCreed σ):
    CatholicismTrue σ := by
  exact TruthCore.Results.Case.Catholicism.FromPrimaViaViaMaximeEns.catholicismFromPrimaViaViaMaximeEns
    σ MovedIn MovesIn (TruthCore.Latin.Aquinas.SummaTheologiae.AdoptedPotency.InPotency InAct CanBe) InAct
    MovesAsMoved MoreIn CausesIn bonum verum
    nobile esse PureAct God hSense
    hPotency hAct hReduction (TruthCore.Results.Aquinas.SummaTheologiae.AdoptedPotencyNonOverlap.nonOverlap InAct CanBe hF1) hPerSe
    hRegress hExcludedMiddle hGrades hApproach hTrue
    hGenus hBeing hCauseMore hName hApplied
    hEM hPureAct hIdentify hAttributes hRevelation
    hJesus hFounded hCatholic hDivineFounding hOnlyTruth
    hProposes
end TruthCore.Results.Case.Catholicism.AdoptedPotency.FromPrimaViaViaMaximeEns
