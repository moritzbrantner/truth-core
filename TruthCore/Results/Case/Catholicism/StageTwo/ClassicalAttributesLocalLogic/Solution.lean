module

public import TruthCore.Results.Case.Catholicism.StageTwo.GodIsPerfect.Solution
public import TruthCore.Results.Case.Catholicism.StageTwo.GodIsOne.Solution
public import TruthCore.Results.Case.Catholicism.StageTwo.GodIsSupremelyGood.Solution
public import TruthCore.Results.Case.Catholicism.StageTwo.GodIsEternal.Solution
public import TruthCore.Results.Case.Catholicism.StageTwo.GodIsInfinite.Solution
public import TruthCore.Results.Case.Catholicism.StageTwo.GodHasWill.Solution

public import TruthCore.Case.Catholicism.ClassicalAttributesLocalLogic

@[expose] public section

namespace TruthCore.Results.Case.Catholicism.StageTwo.ClassicalAttributesLocalLogic
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Greek.Aristotle.Metaphysics (CauseOfQualityInAnotherIsMoreSuchReading)
open TruthCore.Case.Catholicism

/-- Same conclusion and eighteen nonlogical inputs; only the explicit local fragment is added. -/
theorem godHasClassicalAttributes (σ : Signature) {Respect : Type} {Principle : Type}
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
    (hLocal : TruthCore.Case.Catholicism.ClassicalAttributesLocalLogic.LocalLogic σ.IsGod InAct esseOf essenceOf)
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
  -- Equality tests are restricted to actual beings against a God candidate.
  have hOne : GodIsOne σ.IsGod := by
    intro g hg g' hg'
    cases (hLocal g hg).1 g' esse (hMaximal g' hg').1 with
    | inl hSame =>
      exact hSame
    | inr hSame =>
      have hCause := hGenus esse g (hMaximal g hg) g' hSame (hMaximal g' hg').1
      exact ((hMaximal g' hg').2 g
        (hCauseMore g g' esse (fun h => hSame h.symm) hCause)).elim
  have hSimple := TruthCore.Results.Case.Catholicism.StageTwo.GodIsSimple.godIsSimple σ.IsGod
    Composite InAct MoreIn CausesIn esse hMaximal hUniting hCauseMore
  -- Same/other is a Being equality decision, not arbitrary excluded middle.
  have hPerfect : GodIsPerfect σ.IsGod InAct := by
    intro g hg x r hx
    cases (hLocal g hg).1 x r hx with
    | inl hSame => exact hSame ▸ hx
    | inr hSame => exact hPreexist g x r (hGenus esse g (hMaximal g hg) x hSame (hBeing x r hx)) hx
  have hGood := TruthCore.Results.Case.Catholicism.StageTwo.GodIsSupremelyGood.godIsSupremelyGood
    σ.IsGod InAct GoodIn MoreIn CausesIn esse hMaximal hGenus hBeing hGoodness hPerfections
  have hImmutable := TruthCore.Results.Case.Catholicism.StageTwo.GodIsImmutable.godIsImmutable
    σ.IsGod InPotency InAct MoreIn esse PriorSimply hMaximal hFirstBeing hPrior hNotBoth
  have hEternal := TruthCore.Results.Case.Catholicism.StageTwo.GodIsEternal.godIsEternal σ.IsGod
    Eternal InPotency InAct MoreIn esse PriorSimply hMaximal hFirstBeing hPrior hNotBoth hEternity
  -- Stability of this equality suffices; no Principle-wide decision is used.
  have hInfinite : GodIsInfinite σ.IsGod Infinite := by
    intro g hg
    have hOwnEsse : esseOf g = essenceOf g := by
      apply (hLocal g hg).2
      intro hDifferent
      exact hSimple g hg ((hKinds g).2 hDifferent)
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

theorem globalToLocal {Being Respect Principle : Type} (IsGod : Being → Prop)
    (InAct : Being → Respect → Prop) (esseOf essenceOf : Being → Principle)
    (hEM : TruthCore.Logic.ExcludedMiddle) :
    TruthCore.Case.Catholicism.ClassicalAttributesLocalLogic.LocalLogic IsGod InAct esseOf essenceOf := by
  intro g _
  constructor
  · intro x r _
    exact hEM (x = g)
  · intro hnn
    cases hEM (esseOf g = essenceOf g) with
    | inl h => exact h
    | inr h => exact (hnn h).elim
theorem controls : TruthCore.Case.Catholicism.ClassicalAttributesLocalLogic.Controls := by
  unfold TruthCore.Case.Catholicism.ClassicalAttributesLocalLogic.Controls
  dsimp only [
    TruthCore.Case.Catholicism.ClassicalAttributesLocalLogic.ModelBackground,
    TruthCore.Case.Catholicism.ClassicalAttributesLocalLogic.signature,
    TruthCore.Case.Catholicism.ClassicalAttributesLocalLogic.LocalLogic,
    GodIsMaximalInBeing, IsMaximumIn, MaximumInGenusCausesAllInGenusReading,
    CauseOfQualityInAnotherIsMoreSuchReading, CompositeHasAUnitingCauseReading,
    ActualityOnlyInsofarAsBeingReading, PerfectionsOfEffectPreexistInCauseReading,
    GoodnessIsActualityReading, CauseOfBeingCausesEveryPerfection,
    MaximumInBeingIsFirstBeing, ActSimplyPriorToPotencyReading,
    NotActAndPotencyInSameRespectReading, MatterFormAndEsseEssenceAreCompositionsReading,
    SubsistentBeingIsInfiniteReading, ImmutableIsEternalReading,
    NoComponentIsFirstBeingReading, ImmaterialIsIntellectualReading, WillFollowsIntellectReading, CausesAllInGenus, IsFirstBeing]
  repeat first
    | apply And.intro
    | apply Iff.intro
    | exact True.intro
    | exact Or.inl (Subsingleton.elim _ _)
    | exact Subsingleton.elim _ _
    | assumption
    | contradiction
    | exact False.elim (by assumption)
    | intro h
    | exact False.elim (h (Subsingleton.elim _ _))
end TruthCore.Results.Case.Catholicism.StageTwo.ClassicalAttributesLocalLogic
