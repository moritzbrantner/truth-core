import TruthCore.Results.Case.Catholicism.FromPrimaViaWithQ11Uniqueness.Solution
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.AdoptedPotency
namespace TruthCore.Results.Case.Catholicism.AdoptedPotency.FromPrimaViaWithQ11Uniqueness
open TruthCore.Case.Catholicism
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Greek.Aristotle.Metaphysics (CauseOfQualityInAnotherIsMoreSuchReading)

/-- Adopted-potency specialization of `CATHOLICISM-FROM-PRIMA-VIA-WITH-Q11-UNIQUENESS`. Every occurrence of the old
potency parameter, including immutability, priority and sufficiency, is uniformly
`CanBe x r ∧ ¬ InAct x r`. The generic frozen Challenge is retained. F1 supplies
non-overlap; all other original hypotheses retain their existing scope. -/
theorem catholicismFromPrimaViaWithQ11Uniqueness (σ : Signature)
    {Respect : Type}
    {Principle : Type}
    (MovedIn : σ.Being → Respect → Prop)
    (MovesIn : σ.Being → σ.Being → Respect → Prop)
    (CanBe InAct GoodIn : σ.Being → Respect → Prop)
    (MovesAsMoved : σ.Being → σ.Being → Prop)
    (MoreIn : Respect → σ.Being → σ.Being → Prop)
    (CausesIn : σ.Being → σ.Being → Respect → Prop)
    (bonum verum nobile esse : Respect)
    (ComponentOf PriorSimply : σ.Being → σ.Being → Prop)
    (Composite ComposedOfMatterAndForm Infinite Eternal HasIntellect HasWill : σ.Being → Prop)
    (essenceOf esseOf suppositumOf : σ.Being → Principle)
    (deity : Principle)
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
    (hEM : TruthCore.Logic.ExcludedMiddle)
    (hPerfections : CauseOfBeingCausesEveryPerfection InAct CausesIn esse)
    (hNoComponent : NoComponentIsFirstBeingReading ComponentOf PriorSimply)
    (hFirstBeing : MaximumInBeingIsFirstBeing InAct MoreIn esse PriorSimply)
    (hFull : GodNamesTheFullyDescribedPrinciple InAct MoreIn CausesIn esse ComponentOf σ.IsGod)
    (hApplied : CreatedAgentIsAppliedToActByGodReading MovedIn MovesIn CausesIn esse σ.IsGod)
    (hSuffice : ClassicalAttributesSuffice σ (IsSimple Composite) (IsPerfect InAct)
      (IsSupremelyGood InAct GoodIn CausesIn esse) (IsTheOneGod σ.IsGod)
      Infinite (IsImmutable (TruthCore.Latin.Aquinas.SummaTheologiae.AdoptedPotency.InPotency InAct CanBe)) Eternal HasIntellect HasWill)
    (hIndividual : IndividuatingBasisIsIncommunicableReading suppositumOf)
    (hNature : GodSuppositumIsNatureReading σ.IsGod suppositumOf essenceOf)
    (hCommon : ProperGodInstancesHaveCommonNatureReading σ.IsGod essenceOf deity)
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
  sorry
end TruthCore.Results.Case.Catholicism.AdoptedPotency.FromPrimaViaWithQ11Uniqueness
