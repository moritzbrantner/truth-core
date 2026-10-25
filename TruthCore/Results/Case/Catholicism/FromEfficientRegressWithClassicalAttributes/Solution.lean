import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question105.Article5
import TruthCore.Results.Aquinas.SummaTheologiae.MoverRegressFromCauseRegress.Solution
import TruthCore.Results.Case.Catholicism.FirstUnmovedMoverExistsOrNotFromEm.Solution
import TruthCore.Results.Case.Catholicism.FromPrimaViaWithClassicalAttributes.Solution
namespace TruthCore.Results.Case.Catholicism.FromEfficientRegressWithClassicalAttributes
open TruthCore.Case.Catholicism
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Greek.Aristotle.Metaphysics (CauseOfQualityInAnotherIsMoreSuchReading)

/-- Compose the existing efficient-cause regress transfer and excluded-middle
instance into the connected Stage1/Stage2 root proof. The philosophical source
premises, naming converse, revelation/history and teaching-authority bridges
remain open; the historical end is still a structural transcription. -/
theorem catholicismFromEfficientRegressWithClassicalAttributes
    (σ : Signature) {Respect Principle : Type}
    (MovedIn : σ.Being → Respect → Prop)
    (MovesIn : σ.Being → σ.Being → Respect → Prop)
    (InPotency InAct GoodIn : σ.Being → Respect → Prop)
    (MovesAsMoved CausesAsCaused : σ.Being → σ.Being → Prop)
    (MoreIn : Respect → σ.Being → σ.Being → Prop)
    (CausesIn : σ.Being → σ.Being → Respect → Prop)
    (bonum verum nobile esse : Respect)
    (ComponentOf PriorSimply : σ.Being → σ.Being → Prop)
    (Composite ComposedOfMatterAndForm Infinite Eternal HasIntellect HasWill : σ.Being → Prop)
    (essenceOf esseOf : σ.Being → Principle)
    (hSense : SomethingIsMovedReading MovedIn)
    (hPotency : MovedOnlyAsInPotencyReading MovedIn InPotency)
    (hAct : MovesOnlyAsInActReading MovesIn InAct)
    (hReduction : ReducedOnlyByAMoverReading MovedIn MovesIn)
    (hNotBoth : NotActAndPotencyInSameRespectReading InAct InPotency)
    (hPerSe : SecondMoversMoveOnlyAsMovedReading MovedIn MovesIn MovesAsMoved)
    (hCauseRegress : NoInfinitePerSeEfficientCauseSeriesReading CausesAsCaused)
    (hLink : PerSeMoverLinkIsPerSeCauseLinkReading MovesAsMoved CausesAsCaused)
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
      Infinite (IsImmutable InPotency) Eternal HasIntellect HasWill)
    (hMaximal : GodIsMaximalInBeing σ.IsGod InAct MoreIn esse)
    (hUniting : CompositeHasAUnitingCauseReading Composite CausesIn esse)
    (hPreexist : PerfectionsOfEffectPreexistInCauseReading InAct CausesIn esse)
    (hGoodness : GoodnessIsActualityReading GoodIn InAct)
    (hPrior : ActSimplyPriorToPotencyReading InAct InPotency PriorSimply)
    (hKinds : MatterFormAndEsseEssenceAreCompositionsReading ComposedOfMatterAndForm Composite
      essenceOf esseOf)
    (hInfinity : SubsistentBeingIsInfiniteReading essenceOf esseOf Infinite)
    (hEternity : ImmutableIsEternalReading InPotency Eternal)
    (hImmaterial : ImmaterialIsIntellectualReading ComposedOfMatterAndForm HasIntellect ComponentOf)
    (hWillFollows : WillFollowsIntellectReading HasIntellect HasWill)
    (hRevelation : RevelationPossibleAndRecognizable σ)
    (hJesus : JesusClaimedDivineAuthorityAndRose σ)
    (hFounded : ChristFoundedVisibleChurch σ)
    (hCatholic : ChristsChurchIsCatholicChurch σ)
    (hDivineFounding : BridgeChristsChurchFoundedByGod σ)
    (hOnlyTruth : BridgeGodFoundedAuthorityProposesOnlyTruth σ)
    (hProposes : CatholicChurchDefinitivelyProposesCreed σ) :
    CatholicismTrue σ := by
  have hMoverRegress :=
    TruthCore.Results.Aquinas.SummaTheologiae.MoverRegressFromCauseRegress.moverRegressFromCauseRegress
      MovesAsMoved CausesAsCaused hCauseRegress hLink
  have hMoverExistsOrNot :=
    TruthCore.Results.Case.Catholicism.FirstUnmovedMoverExistsOrNotFromEm.firstUnmovedMoverExistsOrNotFromExcludedMiddle
      MovedIn MovesIn hEM
  exact TruthCore.Results.Case.Catholicism.FromPrimaViaWithClassicalAttributes.catholicismFromPrimaViaWithClassicalAttributes
    σ MovedIn MovesIn InPotency InAct GoodIn MovesAsMoved MoreIn CausesIn bonum verum nobile esse
    ComponentOf PriorSimply Composite ComposedOfMatterAndForm Infinite Eternal HasIntellect HasWill
    essenceOf esseOf hSense hPotency hAct hReduction hNotBoth hPerSe hMoverRegress hMoverExistsOrNot
    hGrades hApproach hTrue hGenus hBeing hCauseMore hEM hPerfections hNoComponent hFirstBeing
    hFull hApplied hSuffice hMaximal hUniting hPreexist hGoodness hPrior hKinds hInfinity hEternity
    hImmaterial hWillFollows hRevelation hJesus hFounded hCatholic hDivineFounding hOnlyTruth hProposes
end TruthCore.Results.Case.Catholicism.FromEfficientRegressWithClassicalAttributes
