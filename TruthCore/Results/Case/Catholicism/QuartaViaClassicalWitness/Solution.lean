import TruthCore.Case.Catholicism.StagesOneTwo
import TruthCore.Results.Aquinas.SummaTheologiae.QuartaVia.Solution
import TruthCore.Results.Aquinas.SummaTheologiae.MaximeEnsIsGodViaFullDescription.Solution
import TruthCore.Results.Case.Catholicism.StageTwo.ClassicalAttributesAll.Solution
namespace TruthCore.Results.Case.Catholicism.QuartaViaClassicalWitness
open TruthCore.Case.Catholicism
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Greek.Aristotle.Metaphysics (CauseOfQualityInAnotherIsMoreSuchReading)

/-- Alternative witness from the Fourth Way's explicit four premises; no
maximum-existence or naming converse is added. Source premises remain open. -/
theorem uniqueClassicalGodFromQuartaViaExists (σ : Signature) {Respect : Type} {Principle : Type}
    (InPotency InAct GoodIn : σ.Being → Respect → Prop)
    (MoreIn : Respect → σ.Being → σ.Being → Prop)
    (CausesIn : σ.Being → σ.Being → Respect → Prop)
    (bonum verum nobile esse : Respect)
    (ComponentOf PriorSimply : σ.Being → σ.Being → Prop)
    (Composite ComposedOfMatterAndForm Infinite Eternal HasIntellect HasWill : σ.Being → Prop)
    (essenceOf esseOf : σ.Being → Principle)
    (hNotBoth : NotActAndPotencyInSameRespectReading InAct InPotency)
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
  obtain ⟨m, hm, _⟩ := TruthCore.Results.Aquinas.SummaTheologiae.QuartaVia.quartaVia
    InAct MoreIn CausesIn bonum verum nobile esse hGrades hApproach hTrue hGenus
  have hNamed :=
    TruthCore.Results.Aquinas.SummaTheologiae.MaximeEnsIsGodViaFullDescription.maximeEnsIsGodViaFullDescription
      InAct MoreIn CausesIn esse ComponentOf PriorSimply σ.IsGod hGenus hCauseMore hEM hBeing
      hPerfections hNoComponent hFirstBeing hFull
  have hmGod : σ.IsGod m := hNamed m hm
  -- This local predicate is the domain of the generic attribute theorems;
  -- it does not redefine σ.IsGod or supply its missing naming converse.
  let Maximal : σ.Being → Prop := IsMaximumIn InAct MoreIn esse
  have hIdentity : GodIsMaximalInBeing Maximal InAct MoreIn esse := fun _ h => h
  have hSimple := TruthCore.Results.Case.Catholicism.StageTwo.GodIsSimple.godIsSimple
    Maximal Composite InAct MoreIn CausesIn esse hIdentity hUniting hCauseMore m hm
  have hPerfect := TruthCore.Results.Case.Catholicism.StageTwo.GodIsPerfect.godIsPerfect
    Maximal InAct MoreIn CausesIn esse hIdentity hGenus hBeing hPreexist hEM m hm
  have hGood := TruthCore.Results.Case.Catholicism.StageTwo.GodIsSupremelyGood.godIsSupremelyGood
    Maximal InAct GoodIn MoreIn CausesIn esse hIdentity hGenus hBeing hGoodness hPerfections m hm
  have hImmutable := TruthCore.Results.Case.Catholicism.StageTwo.GodIsImmutable.godIsImmutable
    Maximal InPotency InAct MoreIn esse PriorSimply hIdentity hFirstBeing hPrior hNotBoth m hm
  have hEternal := TruthCore.Results.Case.Catholicism.StageTwo.GodIsEternal.godIsEternal
    Maximal Eternal InPotency InAct MoreIn esse PriorSimply hIdentity hFirstBeing hPrior hNotBoth
    hEternity m hm
  have hInfinite := TruthCore.Results.Case.Catholicism.StageTwo.GodIsInfinite.godIsInfinite
    Maximal Composite ComposedOfMatterAndForm Infinite essenceOf esseOf InAct MoreIn CausesIn esse
    hIdentity hUniting hCauseMore hKinds hEM hInfinity m hm
  have hIntellect := TruthCore.Results.Case.Catholicism.StageTwo.GodHasIntellect.godHasIntellect
    Maximal Composite ComposedOfMatterAndForm HasIntellect ComponentOf PriorSimply essenceOf esseOf
    InAct MoreIn CausesIn esse hIdentity hUniting hCauseMore hKinds hNoComponent hFirstBeing
    hImmaterial m hm
  have hWill := TruthCore.Results.Case.Catholicism.StageTwo.GodHasWill.godHasWill
    Maximal Composite ComposedOfMatterAndForm HasIntellect HasWill ComponentOf PriorSimply
    essenceOf esseOf InAct MoreIn CausesIn esse hIdentity hUniting hCauseMore hKinds hNoComponent
    hFirstBeing hImmaterial hWillFollows m hm
  -- Only the ninth attribute uses the original universal naming premise.
  -- Uniqueness of maxima alone would not exclude another nonmaximal IsGod.
  have hOne := TruthCore.Results.Case.Catholicism.StageTwo.GodIsOne.godIsOne
    σ.IsGod InAct MoreIn CausesIn esse hMaximal hGenus hCauseMore hEM m hmGod
  -- The checked bridge equivalence groups only attributes of this same witness.
  have hField := classicalAttributesFromNine σ (IsSimple Composite) (IsPerfect InAct)
    (IsSupremelyGood InAct GoodIn CausesIn esse) (IsTheOneGod σ.IsGod)
    Infinite (IsImmutable InPotency) Eternal HasIntellect HasWill hSuffice m
    ⟨hSimple, hPerfect, hGood, hOne, hInfinite, hImmutable, hEternal, hIntellect, hWill⟩
  exact ⟨m, hmGod, hOne, hField⟩
end TruthCore.Results.Case.Catholicism.QuartaViaClassicalWitness
