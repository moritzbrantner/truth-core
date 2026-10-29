import TruthCore.Results.Case.Catholicism.StageTwo.GodIsPerfect.Solution
import TruthCore.Results.Case.Catholicism.StageTwo.GodIsOne.Solution
import TruthCore.Results.Case.Catholicism.StageTwo.GodIsSupremelyGood.Solution
import TruthCore.Results.Case.Catholicism.StageTwo.GodIsEternal.Solution
import TruthCore.Results.Case.Catholicism.StageTwo.GodIsInfinite.Solution
import TruthCore.Results.Case.Catholicism.StageTwo.GodHasWill.Solution
namespace TruthCore.Results.Case.Catholicism.StageTwo.ClassicalAttributesIdentity
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Greek.Aristotle.Metaphysics (CauseOfQualityInAnotherIsMoreSuchReading)
open TruthCore.Case.Catholicism

/-- Separate sufficient logical floor: decidable equality on Being and Principle.
No full excluded middle, choice, or necessity/minimality assertion.
Conditional assembly at one being. The nine derived predicates imply the
primitive field only under the explicit open sufficiency premise; the
God-to-maximality naming converse is retained. This universal conditional
supplies no existence witness. -/
theorem godHasClassicalAttributes (σ : Signature) {Respect : Type} {Principle : Type}
    [DecidableEq σ.Being] [DecidableEq Principle]
    (InPotency InAct GoodIn : σ.Being → Respect → Prop)
    (MoreIn : Respect → σ.Being → σ.Being → Prop)
    (CausesIn : σ.Being → σ.Being → Respect → Prop) (esse : Respect)
    (ComponentOf PriorSimply : σ.Being → σ.Being → Prop)
    (Composite ComposedOfMatterAndForm Infinite Eternal HasIntellect HasWill : σ.Being → Prop)
    (essenceOf esseOf : σ.Being → Principle)
    (hSuffice : ClassicalAttributesSuffice σ (IsSimple Composite) (IsPerfect InAct)
      (IsSupremelyGood InAct GoodIn CausesIn esse) (IsTheOneGod σ.IsGod)
      Infinite (IsImmutable InPotency) Eternal HasIntellect HasWill)
    (hMaximal : GodIsMaximalInBeing σ.IsGod InAct MoreIn esse)
    (hGenus : MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn)
    (hCauseMore : CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn)
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
    (hNoComponent : NoComponentIsFirstBeingReading ComponentOf PriorSimply)
    (hImmaterial : ImmaterialIsIntellectualReading ComposedOfMatterAndForm HasIntellect
      ComponentOf)
    (hWillFollows : WillFollowsIntellectReading HasIntellect HasWill) :
    GodHasClassicalAttributes σ := by
  -- Identity decisions on Being suffice for uniqueness of maxima.
  have hOne : GodIsOne σ.IsGod := by
    intro g hg g' hg'
    by_cases hSame : g' = g
    · exact hSame
    · have hCause := hGenus esse g (hMaximal g hg) g' hSame (hMaximal g' hg').1
      exact ((hMaximal g' hg').2 g
        (hCauseMore g g' esse (fun h => hSame h.symm) hCause)).elim
  have hSimple := TruthCore.Results.Case.Catholicism.StageTwo.GodIsSimple.godIsSimple σ.IsGod
    Composite InAct MoreIn CausesIn esse hMaximal hUniting hCauseMore
  -- Same/other is a Being equality decision, not arbitrary excluded middle.
  have hPerfect : GodIsPerfect σ.IsGod InAct := by
    intro g hg x r hx
    by_cases hSame : x = g
    · exact hSame ▸ hx
    · exact hPreexist g x r (hGenus esse g (hMaximal g hg) x hSame (hBeing x r hx)) hx
  have hGood := TruthCore.Results.Case.Catholicism.StageTwo.GodIsSupremelyGood.godIsSupremelyGood
    σ.IsGod InAct GoodIn MoreIn CausesIn esse hMaximal hGenus hBeing hGoodness hPerfections
  have hImmutable := TruthCore.Results.Case.Catholicism.StageTwo.GodIsImmutable.godIsImmutable
    σ.IsGod InPotency InAct MoreIn esse PriorSimply hMaximal hFirstBeing hPrior hNotBoth
  have hEternal := TruthCore.Results.Case.Catholicism.StageTwo.GodIsEternal.godIsEternal σ.IsGod
    Eternal InPotency InAct MoreIn esse PriorSimply hMaximal hFirstBeing hPrior hNotBoth hEternity
  -- A separate Principle identity decision recovers positive esse/essence identity.
  have hInfinite : GodIsInfinite σ.IsGod Infinite := by
    intro g hg
    have hOwnEsse : esseOf g = essenceOf g := by
      by_cases hSame : esseOf g = essenceOf g
      · exact hSame
      · exact (hSimple g hg ((hKinds g).2 hSame)).elim
    exact hInfinity g hOwnEsse
  have hIntellect := TruthCore.Results.Case.Catholicism.StageTwo.GodHasIntellect.godHasIntellect
    σ.IsGod Composite ComposedOfMatterAndForm HasIntellect ComponentOf PriorSimply essenceOf esseOf
    InAct MoreIn CausesIn esse hMaximal hUniting hCauseMore hKinds hNoComponent hFirstBeing
    hImmaterial
  have hWill := TruthCore.Results.Case.Catholicism.StageTwo.GodHasWill.godHasWill σ.IsGod Composite
    ComposedOfMatterAndForm HasIntellect HasWill ComponentOf PriorSimply essenceOf esseOf InAct MoreIn
    CausesIn esse hMaximal hUniting hCauseMore hKinds hNoComponent hFirstBeing hImmaterial
    hWillFollows
  -- INF-STAGE2-CLASSICAL-ATTRIBUTES-ALL
  intro g hg
  exact classicalAttributesFromNine σ (IsSimple Composite) (IsPerfect InAct)
    (IsSupremelyGood InAct GoodIn CausesIn esse) (IsTheOneGod σ.IsGod)
    Infinite (IsImmutable InPotency) Eternal HasIntellect HasWill hSuffice g
    ⟨hSimple g hg, hPerfect g hg, hGood g hg, hOne g hg, hInfinite g hg,
      hImmutable g hg, hEternal g hg, hIntellect g hg, hWill g hg⟩

end TruthCore.Results.Case.Catholicism.StageTwo.ClassicalAttributesIdentity
