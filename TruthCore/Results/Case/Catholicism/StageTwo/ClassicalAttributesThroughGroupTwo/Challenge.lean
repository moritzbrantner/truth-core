import TruthCore.Results.Case.Catholicism.StageTwo.GodIsPerfect.Solution
import TruthCore.Results.Case.Catholicism.StageTwo.GodIsOne.Solution
import TruthCore.Results.Case.Catholicism.StageTwo.GodIsSupremelyGood.Solution
import TruthCore.Results.Case.Catholicism.StageTwo.GodIsEternal.Solution
import TruthCore.Results.Case.Catholicism.StageTwo.GodIsInfinite.Solution
namespace TruthCore.Results.Case.Catholicism.StageTwo.ClassicalAttributesThroughGroupTwo
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Greek.Aristotle.Metaphysics (CauseOfQualityInAnotherIsMoreSuchReading)
open TruthCore.Case.Catholicism
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
    (hPrior : ActSimplyPriorToPotencyReading InAct InPotency PriorSimply)
    (hNotBoth : NotActAndPotencyInSameRespectReading InAct InPotency)
    (hKinds : MatterFormAndEsseEssenceAreCompositionsReading ComposedOfMatterAndForm Composite
      essenceOf esseOf)
    (hInfinity : SubsistentBeingIsInfiniteReading essenceOf esseOf Infinite)
    (hEternity : ImmutableIsEternalReading InPotency Eternal)
    (hIntellect : GodHasIntellect σ.IsGod HasIntellect)
    (hWill : GodHasWill σ.IsGod HasWill) :
    GodHasClassicalAttributes σ := by
  sorry
end TruthCore.Results.Case.Catholicism.StageTwo.ClassicalAttributesThroughGroupTwo
