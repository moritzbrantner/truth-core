module

public import TruthCore.Results.Case.Catholicism.FromEfficientRegressWithClassicalAttributesIdentity.Solution
public import TruthCore.Results.Aquinas.SummaTheologiae.AdoptedPotencyNonOverlap.Solution

@[expose] public section

namespace TruthCore.Results.Case.Catholicism.AdoptedPotency.FromEfficientRegressWithClassicalAttributesIdentity
open TruthCore.Case.Catholicism
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Greek.Aristotle.Metaphysics (CauseOfQualityInAnotherIsMoreSuchReading)

/-- Adopted-potency specialization of `CATHOLICISM-FROM-EFFICIENT-REGRESS-WITH-CLASSICAL-ATTRIBUTES-IDENTITY`. Every occurrence of the old
potency parameter, including immutability, priority and sufficiency, is uniformly
`CanBe x r ∧ ¬ InAct x r`. The generic frozen Challenge is retained. F1 supplies
non-overlap; all other original hypotheses retain their existing scope. -/
theorem catholicismFromEfficientRegressWithClassicalAttributes (σ : Signature)
    {Respect Principle : Type}
    [DecidableEq σ.Being]
    [DecidableEq Principle]
    (MovedIn : σ.Being → Respect → Prop)
    (MovesIn : σ.Being → σ.Being → Respect → Prop)
    (CanBe InAct GoodIn : σ.Being → Respect → Prop)
    (MovesAsMoved CausesAsCaused : σ.Being → σ.Being → Prop)
    (MoreIn : Respect → σ.Being → σ.Being → Prop)
    (CausesIn : σ.Being → σ.Being → Respect → Prop)
    (bonum verum nobile esse : Respect)
    (ComponentOf PriorSimply : σ.Being → σ.Being → Prop)
    (Composite ComposedOfMatterAndForm Infinite Eternal HasIntellect HasWill : σ.Being → Prop)
    (essenceOf esseOf : σ.Being → Principle)
    (hSense : SomethingIsMovedReading MovedIn)
    (hPotency : MovedOnlyAsInPotencyReading MovedIn (TruthCore.Latin.Aquinas.SummaTheologiae.AdoptedPotency.InPotency InAct CanBe))
    (hAct : MovesOnlyAsInActReading MovesIn InAct)
    (hReduction : ReducedOnlyByAMoverReading MovedIn MovesIn)
    (hF1 : TruthCore.Logic.CaseNonContradiction.CasePredicateNonContradiction.{1, 1})
    (hPerSe : SecondMoversMoveOnlyAsMovedReading MovedIn MovesIn MovesAsMoved)
    (hCauseRegress : NoInfinitePerSeEfficientCauseSeriesReading CausesAsCaused)
    (hLink : PerSeMoverLinkIsPerSeCauseLinkReading MovesAsMoved CausesAsCaused)
    (hMoverExistsOrNot : FirstUnmovedMoverExistsOrNot MovedIn MovesIn)
    (hGrades : GradesFoundInThingsReading MoreIn bonum verum nobile)
    (hApproach : GradesByApproachToAMaximumReading InAct MoreIn)
    (hTrue : MostTrueIsMostBeingReading InAct MoreIn verum esse)
    (hGenus : MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn)
    (hBeing : ActualityOnlyInsofarAsBeingReading InAct esse)
    (hCauseMore : CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn)
    (hPerfections : CauseOfBeingCausesEveryPerfection InAct CausesIn esse)
    (hNoComponent : NoComponentIsFirstBeingReading ComponentOf PriorSimply)
    (hFirstBeing : MaximumInBeingIsFirstBeing InAct MoreIn esse PriorSimply)
    (hFull : GodNamesTheFullyDescribedPrinciple InAct MoreIn CausesIn esse ComponentOf σ.IsGod)
    (hApplied : CreatedAgentIsAppliedToActByGodReading MovedIn MovesIn CausesIn esse σ.IsGod)
    (hSuffice : ClassicalAttributesSuffice σ (IsSimple Composite) (IsPerfect InAct)
      (IsSupremelyGood InAct GoodIn CausesIn esse) (IsTheOneGod σ.IsGod)
      Infinite (IsImmutable (TruthCore.Latin.Aquinas.SummaTheologiae.AdoptedPotency.InPotency InAct CanBe)) Eternal HasIntellect HasWill)
    (hMaximal : GodIsMaximalInBeing σ.IsGod InAct MoreIn esse)
    (hUniting : CompositeHasAUnitingCauseReading Composite CausesIn esse)
    (hPreexist : PerfectionsOfEffectPreexistInCauseReading InAct CausesIn esse)
    (hGoodness : GoodnessIsActualityReading GoodIn InAct)
    (hPrior : ActSimplyPriorToPotencyReading InAct (TruthCore.Latin.Aquinas.SummaTheologiae.AdoptedPotency.InPotency InAct CanBe) PriorSimply)
    (hKinds : MatterFormAndEsseEssenceAreCompositionsReading ComposedOfMatterAndForm Composite
      essenceOf esseOf)
    (hInfinity : SubsistentBeingIsInfiniteReading essenceOf esseOf Infinite)
    (hEternity : ImmutableIsEternalReading (TruthCore.Latin.Aquinas.SummaTheologiae.AdoptedPotency.InPotency InAct CanBe) Eternal)
    (hImmaterial : ImmaterialIsIntellectualReading ComposedOfMatterAndForm HasIntellect ComponentOf)
    (hWillFollows : WillFollowsIntellectReading HasIntellect HasWill)
    (hRevelation : RevelationPossibleAndRecognizable σ)
    (hJesus : JesusClaimedDivineAuthorityAndRose σ)
    (hFounded : ChristFoundedVisibleChurch σ)
    (hCatholic : ChristsChurchIsCatholicChurch σ)
    (hDivineFounding : BridgeChristsChurchFoundedByGod σ)
    (hOnlyTruth : BridgeGodFoundedAuthorityProposesOnlyTruth σ)
    (hProposes : CatholicChurchDefinitivelyProposesCreed σ):
    CatholicismTrue σ := by
  exact TruthCore.Results.Case.Catholicism.FromEfficientRegressWithClassicalAttributesIdentity.catholicismFromEfficientRegressWithClassicalAttributes
    σ MovedIn MovesIn (TruthCore.Latin.Aquinas.SummaTheologiae.AdoptedPotency.InPotency InAct CanBe) InAct
    GoodIn MovesAsMoved CausesAsCaused MoreIn CausesIn
    bonum verum nobile esse ComponentOf
    PriorSimply Composite ComposedOfMatterAndForm Infinite Eternal
    HasIntellect HasWill essenceOf esseOf hSense
    hPotency hAct hReduction (TruthCore.Results.Aquinas.SummaTheologiae.AdoptedPotencyNonOverlap.nonOverlap InAct CanBe hF1) hPerSe
    hCauseRegress hLink hMoverExistsOrNot hGrades hApproach
    hTrue hGenus hBeing hCauseMore hPerfections
    hNoComponent hFirstBeing hFull hApplied hSuffice
    hMaximal hUniting hPreexist hGoodness hPrior
    hKinds hInfinity hEternity hImmaterial hWillFollows
    hRevelation hJesus hFounded hCatholic hDivineFounding
    hOnlyTruth hProposes
end TruthCore.Results.Case.Catholicism.AdoptedPotency.FromEfficientRegressWithClassicalAttributesIdentity
