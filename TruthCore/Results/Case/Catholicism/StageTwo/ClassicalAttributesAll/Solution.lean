import TruthCore.Results.Case.Catholicism.StageTwo.GodIsOne.Solution
import TruthCore.Results.Case.Catholicism.StageTwo.GodIsSupremelyGood.Solution
import TruthCore.Results.Case.Catholicism.StageTwo.GodIsEternal.Solution
import TruthCore.Results.Case.Catholicism.StageTwo.GodIsInfinite.Solution
import TruthCore.Results.Case.Catholicism.StageTwo.GodHasWill.Solution
namespace TruthCore.Results.Case.Catholicism.StageTwo.ClassicalAttributesAll
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Greek.Aristotle.Metaphysics (CauseOfQualityInAnotherIsMoreSuchReading)
open TruthCore.Case.Catholicism

/-- Stage 2, complete: all nine attributes of the definitional bridge are
derived for whatever is God (one, simple, perfect, supremely good, infinite,
immutable, eternal, intellect, will). -/
theorem godHasClassicalAttributes (σ : Signature) {Respect : Type} {Principle : Type}
    (MovedIn InPotency InAct GoodIn : σ.Being → Respect → Prop)
    (MovesIn : σ.Being → σ.Being → Respect → Prop)
    (MoreIn : Respect → σ.Being → σ.Being → Prop)
    (CausesIn : σ.Being → σ.Being → Respect → Prop) (esse : Respect)
    (Composite ComposedOfMatterAndForm Infinite Eternal HasIntellect HasWill : σ.Being → Prop)
    (essenceOf esseOf : σ.Being → Principle)
    (hSuffice : ClassicalAttributesSuffice σ (IsSimple Composite) (IsPerfect InAct)
      (IsSupremelyGood InAct GoodIn CausesIn esse) (IsTheOneGod σ.IsGod)
      Infinite (IsImmutable MovedIn) Eternal HasIntellect HasWill)
    (hMaximal : GodIsMaximalInBeing σ.IsGod InAct MoreIn esse)
    (hGenus : MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn)
    (hCauseMore : CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn)
    (hEM : TruthCore.Logic.ExcludedMiddle)
    (hUniting : CompositeHasAUnitingCauseReading Composite CausesIn esse)
    (hBeing : ActualityOnlyInsofarAsBeingReading InAct esse)
    (hPreexist : PerfectionsOfEffectPreexistInCauseReading InAct CausesIn esse)
    (hGoodness : GoodnessIsActualityReading GoodIn InAct)
    (hPerfections : CauseOfBeingCausesEveryPerfection InAct CausesIn esse)
    (hReduction : ReducedOnlyByAMoverReading MovedIn MovesIn)
    (hAct : MovesOnlyAsInActReading MovesIn InAct)
    (hPotency : MovedOnlyAsInPotencyReading MovedIn InPotency)
    (hNotBoth : NotActAndPotencyInSameRespectReading InAct InPotency)
    (hKinds : MatterFormAndEsseEssenceAreCompositionsReading ComposedOfMatterAndForm Composite
      essenceOf esseOf)
    (hInfinity : SubsistentBeingIsInfiniteReading essenceOf esseOf Infinite)
    (hEternity : ImmutableIsEternalReading MovedIn Eternal)
    (hImmaterial : ImmaterialIsIntellectualReading ComposedOfMatterAndForm HasIntellect)
    (hWillFollows : WillFollowsIntellectReading HasIntellect HasWill) :
    GodHasClassicalAttributes σ := by
  have hOne := TruthCore.Results.Case.Catholicism.StageTwo.GodIsOne.godIsOne σ.IsGod InAct MoreIn
    CausesIn esse hMaximal hGenus hCauseMore hEM
  have hSimple := TruthCore.Results.Case.Catholicism.StageTwo.GodIsSimple.godIsSimple σ.IsGod
    Composite InAct MoreIn CausesIn esse hMaximal hUniting hCauseMore
  have hPerfect := TruthCore.Results.Case.Catholicism.StageTwo.GodIsPerfect.godIsPerfect σ.IsGod
    InAct MoreIn CausesIn esse hMaximal hGenus hBeing hPreexist hEM
  have hGood := TruthCore.Results.Case.Catholicism.StageTwo.GodIsSupremelyGood.godIsSupremelyGood
    σ.IsGod InAct GoodIn MoreIn CausesIn esse hMaximal hGenus hBeing hGoodness hPerfections
  have hImmutable := TruthCore.Results.Case.Catholicism.StageTwo.GodIsImmutable.godIsImmutable
    σ.IsGod MovedIn MovesIn InPotency InAct MoreIn CausesIn esse hMaximal hGenus hBeing hPreexist
    hEM hReduction hAct hPotency hNotBoth
  have hEternal := TruthCore.Results.Case.Catholicism.StageTwo.GodIsEternal.godIsEternal σ.IsGod
    Eternal MovedIn MovesIn InPotency InAct MoreIn CausesIn esse hMaximal hGenus hBeing hPreexist
    hEM hReduction hAct hPotency hNotBoth hEternity
  have hInfinite := TruthCore.Results.Case.Catholicism.StageTwo.GodIsInfinite.godIsInfinite
    σ.IsGod Composite ComposedOfMatterAndForm Infinite essenceOf esseOf InAct MoreIn CausesIn esse
    hMaximal hUniting hCauseMore hKinds hEM hInfinity
  have hIntellect := TruthCore.Results.Case.Catholicism.StageTwo.GodHasIntellect.godHasIntellect
    σ.IsGod Composite ComposedOfMatterAndForm HasIntellect essenceOf esseOf InAct MoreIn CausesIn esse
    hMaximal hUniting hCauseMore hKinds hImmaterial
  have hWill := TruthCore.Results.Case.Catholicism.StageTwo.GodHasWill.godHasWill σ.IsGod Composite
    ComposedOfMatterAndForm HasIntellect HasWill essenceOf esseOf InAct MoreIn CausesIn esse hMaximal
    hUniting hCauseMore hKinds hImmaterial hWillFollows
  -- INF-STAGE2-CLASSICAL-ATTRIBUTES-ALL
  intro g hg
  exact hSuffice g (hSimple g hg) (hPerfect g hg) (hGood g hg) (hOne g hg) (hInfinite g hg)
    (hImmutable g hg) (hEternal g hg) (hIntellect g hg) (hWill g hg)

end TruthCore.Results.Case.Catholicism.StageTwo.ClassicalAttributesAll
