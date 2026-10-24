import TruthCore.Results.Case.Catholicism.StageTwo.GodIsPerfect.Solution
import TruthCore.Results.Case.Catholicism.StageTwo.GodIsOne.Solution
import TruthCore.Results.Case.Catholicism.StageTwo.GodIsSupremelyGood.Solution
import TruthCore.Results.Case.Catholicism.StageTwo.GodIsEternal.Solution
import TruthCore.Results.Case.Catholicism.StageTwo.GodIsInfinite.Solution
namespace TruthCore.Results.Case.Catholicism.StageTwo.ClassicalAttributesThroughGroupTwo
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Greek.Aristotle.Metaphysics (CauseOfQualityInAnotherIsMoreSuchReading)
open TruthCore.Case.Catholicism

/-- Stage 2 through group 2: seven of the nine attributes of the definitional
bridge are derived (one, simple, perfect, supremely good, infinite, immutable,
eternal); intellect and will stay open premises until group 3. -/
theorem godHasClassicalAttributes (σ : Signature) {Respect : Type} {Principle : Type}
    (InPotency InAct GoodIn : σ.Being → Respect → Prop)
    (MoreIn : Respect → σ.Being → σ.Being → Prop)
    (CausesIn : σ.Being → σ.Being → Respect → Prop) (esse : Respect)
    (PriorSimply : σ.Being → σ.Being → Prop)
    (Composite ComposedOfMatterAndForm Infinite Eternal HasIntellect HasWill : σ.Being → Prop)
    (essenceOf esseOf : σ.Being → Principle)
    (hSuffice : ClassicalAttributesSuffice σ (IsSimple Composite) (IsPerfect InAct)
      (IsSupremelyGood InAct GoodIn CausesIn esse) (IsTheOneGod σ.IsGod)
      Infinite (IsImmutable InPotency) Eternal HasIntellect HasWill)
    (hMaximal : GodIsMaximalInBeing σ.IsGod InAct MoreIn esse)
    (hGenus : MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn)
    (hCauseMore : CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn)
    (hEM : TruthCore.Logic.ExcludedMiddle)
    (hUniting : CompositeHasAUnitingCauseReading Composite CausesIn esse)
    (hBeing : ActualityOnlyInsofarAsBeingReading InAct esse)
    (hPreexist : PerfectionsOfEffectPreexistInCauseReading InAct CausesIn esse)
    (hGoodness : GoodnessIsActualityReading GoodIn InAct)
    (hPerfections : CauseOfBeingCausesEveryPerfection InAct CausesIn esse)
    (hFirstBeing : MaximumInBeingIsFirstBeing InAct MoreIn esse PriorSimply)
    (hPureAct : FirstBeingIsInNoWayInPotencyReading InPotency PriorSimply)
    (hKinds : MatterFormAndEsseEssenceAreCompositionsReading ComposedOfMatterAndForm Composite
      essenceOf esseOf)
    (hInfinity : SubsistentBeingIsInfiniteReading essenceOf esseOf Infinite)
    (hEternity : ImmutableIsEternalReading InPotency Eternal)
    (hIntellect : GodHasIntellect σ.IsGod HasIntellect)
    (hWill : GodHasWill σ.IsGod HasWill) :
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
    σ.IsGod InPotency InAct MoreIn esse PriorSimply hMaximal hFirstBeing hPureAct
  have hEternal := TruthCore.Results.Case.Catholicism.StageTwo.GodIsEternal.godIsEternal σ.IsGod
    Eternal InPotency InAct MoreIn esse PriorSimply hMaximal hFirstBeing hPureAct hEternity
  have hInfinite := TruthCore.Results.Case.Catholicism.StageTwo.GodIsInfinite.godIsInfinite
    σ.IsGod Composite ComposedOfMatterAndForm Infinite essenceOf esseOf InAct MoreIn CausesIn esse
    hMaximal hUniting hCauseMore hKinds hEM hInfinity
  -- INF-STAGE2-CLASSICAL-ATTRIBUTES-THROUGH-GROUP-TWO
  intro g hg
  exact hSuffice g (hSimple g hg) (hPerfect g hg) (hGood g hg) (hOne g hg) (hInfinite g hg)
    (hImmutable g hg) (hEternal g hg) (hIntellect g hg) (hWill g hg)

end TruthCore.Results.Case.Catholicism.StageTwo.ClassicalAttributesThroughGroupTwo
