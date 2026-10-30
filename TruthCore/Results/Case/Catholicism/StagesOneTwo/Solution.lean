import TruthCore.Case.Catholicism.StagesOneTwo
import TruthCore.Results.Case.Catholicism.StageOneViaFullDescription.Solution
import TruthCore.Results.Aquinas.SummaTheologiae.PrimaVia.Solution
import TruthCore.Results.Case.Catholicism.StageTwo.ClassicalAttributesAll.Solution
namespace TruthCore.Results.Case.Catholicism.StagesOneTwo
open TruthCore.Case.Catholicism
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Greek.Aristotle.Metaphysics (CauseOfQualityInAnotherIsMoreSuchReading)

/-- Connect the existing First/Fourth Way and full-description naming results
to all nine Stage2 attribute proofs at the same witness. The original
GodIsMaximalInBeing premise is still used here for the global uniqueness
attribute (the alternative CATHOLICISM-STAGES-ONE-TWO-Q11-NATURE does without it); no converse of the nominal definition is inferred. Philosophical
source premises and ClassicalAttributesSuffice remain open. -/
theorem uniqueClassicalGodExists (σ : Signature) {Respect : Type} {Principle : Type}
    (MovedIn : σ.Being → Respect → Prop)
    (MovesIn : σ.Being → σ.Being → Respect → Prop)
    (InPotency InAct GoodIn : σ.Being → Respect → Prop)
    (MovesAsMoved : σ.Being → σ.Being → Prop)
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
    (hWillFollows : WillFollowsIntellectReading HasIntellect HasWill) :
    UniqueClassicalGodExists σ := by
  -- Retain the first mover and its maximality; the older Stage1 conclusion
  -- existentially forgets maximality, so compose its verified components here.
  have hFirstWay := TruthCore.Results.Aquinas.SummaTheologiae.PrimaVia.primaVia
    MovedIn MovesIn InPotency InAct MovesAsMoved
    hSense hPotency hAct hReduction hNotBoth hPerSe hRegress
  have hExists : ThereIsAFirstUnmovedMover MovedIn MovesIn := by
    cases hExcludedMiddle with
    | inl h => exact h
    | inr hNone => exact absurd hNone hFirstWay
  obtain ⟨f, hf⟩ := hExists
  obtain ⟨m, hm, _⟩ := TruthCore.Results.Aquinas.SummaTheologiae.QuartaVia.quartaVia
    InAct MoreIn CausesIn bonum verum nobile esse hGrades hApproach hTrue hGenus
  have hNamed :=
    TruthCore.Results.Aquinas.SummaTheologiae.MaximeEnsIsGodViaFullDescription.maximeEnsIsGodViaFullDescription
      InAct MoreIn CausesIn esse ComponentOf PriorSimply σ.IsGod hGenus hCauseMore hEM hBeing
      hPerfections hNoComponent hFirstBeing hFull
  have hSame := TruthCore.Results.Aquinas.SummaTheologiae.FirstMoverIsMaximeEns.firstMoverIsMaximeEns
    MovedIn MovesIn InAct MoreIn CausesIn esse σ.IsGod hGenus hAct hBeing hNamed hApplied hEM
    f hf m hm
  have hfMax : IsMaximumIn InAct MoreIn esse f := hSame.symm ▸ hm
  have hfGod : σ.IsGod f := hNamed f hfMax
  -- This local predicate is the domain of the generic attribute theorems;
  -- it does not redefine σ.IsGod or supply its missing naming converse.
  let Maximal : σ.Being → Prop := IsMaximumIn InAct MoreIn esse
  have hIdentity : GodIsMaximalInBeing Maximal InAct MoreIn esse := fun _ h => h
  have hSimple := TruthCore.Results.Case.Catholicism.StageTwo.GodIsSimple.godIsSimple
    Maximal Composite InAct MoreIn CausesIn esse hIdentity hUniting hCauseMore f hfMax
  have hPerfect := TruthCore.Results.Case.Catholicism.StageTwo.GodIsPerfect.godIsPerfect
    Maximal InAct MoreIn CausesIn esse hIdentity hGenus hBeing hPreexist hEM f hfMax
  have hGood := TruthCore.Results.Case.Catholicism.StageTwo.GodIsSupremelyGood.godIsSupremelyGood
    Maximal InAct GoodIn MoreIn CausesIn esse hIdentity hGenus hBeing hGoodness hPerfections f hfMax
  have hImmutable := TruthCore.Results.Case.Catholicism.StageTwo.GodIsImmutable.godIsImmutable
    Maximal InPotency InAct MoreIn esse PriorSimply hIdentity hFirstBeing hPrior hNotBoth f hfMax
  have hEternal := TruthCore.Results.Case.Catholicism.StageTwo.GodIsEternal.godIsEternal
    Maximal Eternal InPotency InAct MoreIn esse PriorSimply hIdentity hFirstBeing hPrior hNotBoth
    hEternity f hfMax
  have hInfinite := TruthCore.Results.Case.Catholicism.StageTwo.GodIsInfinite.godIsInfinite
    Maximal Composite ComposedOfMatterAndForm Infinite essenceOf esseOf InAct MoreIn CausesIn esse
    hIdentity hUniting hCauseMore hKinds hEM hInfinity f hfMax
  have hIntellect := TruthCore.Results.Case.Catholicism.StageTwo.GodHasIntellect.godHasIntellect
    Maximal Composite ComposedOfMatterAndForm HasIntellect ComponentOf PriorSimply essenceOf esseOf
    InAct MoreIn CausesIn esse hIdentity hUniting hCauseMore hKinds hNoComponent hFirstBeing
    hImmaterial f hfMax
  have hWill := TruthCore.Results.Case.Catholicism.StageTwo.GodHasWill.godHasWill
    Maximal Composite ComposedOfMatterAndForm HasIntellect HasWill ComponentOf PriorSimply
    essenceOf esseOf InAct MoreIn CausesIn esse hIdentity hUniting hCauseMore hKinds hNoComponent
    hFirstBeing hImmaterial hWillFollows f hfMax
  -- Only the ninth attribute uses the original universal naming premise.
  -- Uniqueness of maxima is not used to exclude another nonmaximal IsGod.
  have hOne := TruthCore.Results.Case.Catholicism.StageTwo.GodIsOne.godIsOne
    σ.IsGod InAct MoreIn CausesIn esse hMaximal hGenus hCauseMore hEM f hfGod
  -- The checked bridge equivalence groups only attributes of this same witness.
  have hField := classicalAttributesFromNine σ (IsSimple Composite) (IsPerfect InAct)
    (IsSupremelyGood InAct GoodIn CausesIn esse) (IsTheOneGod σ.IsGod)
    Infinite (IsImmutable InPotency) Eternal HasIntellect HasWill hSuffice f
    ⟨hSimple, hPerfect, hGood, hOne, hInfinite, hImmutable, hEternal, hIntellect, hWill⟩
  exact ⟨f, hfGod, hOne, hField⟩
end TruthCore.Results.Case.Catholicism.StagesOneTwo
