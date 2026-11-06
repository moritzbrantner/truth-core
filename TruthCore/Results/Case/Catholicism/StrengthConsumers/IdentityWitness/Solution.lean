module

public import TruthCore.Results.Case.Catholicism.StagesOneTwoIdentity.Solution

@[expose] public section

namespace TruthCore.Results.Case.Catholicism.StrengthConsumers.IdentityWitness
open TruthCore.Case.Catholicism
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Greek.Aristotle.Metaphysics (CauseOfQualityInAnotherIsMoreSuchReading)

/-- Analyst composition audit: the same conclusion from the displayed reduced
bundle. The Fourth-Way maximum supplies the witness directly. The frozen
legacy theorem remains unchanged; no premise truth or global minimality follows. -/
theorem uniqueClassicalGodIdentityWithoutMotion (σ : Signature) {Respect : Type} {Principle : Type}
    [DecidableEq σ.Being] [DecidableEq Principle]
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
    TruthCore.Results.Aquinas.SummaTheologiae.MaximeEnsIsGodViaFullDescriptionIdentity.maximeEnsIsGodViaFullDescription
      InAct MoreIn CausesIn esse ComponentOf PriorSimply σ.IsGod hGenus hCauseMore hBeing
      hPerfections hNoComponent hFirstBeing hFull
  have hfGod := hNamed m hm
  -- The attribute interface matches the retained original hMaximal premise.
  -- It is applied at m, with σ.IsGod unchanged throughout.
  have hAttributes :=
    TruthCore.Results.Case.Catholicism.StageTwo.ClassicalAttributesIdentity.godHasClassicalAttributes
      σ InPotency InAct GoodIn MoreIn CausesIn esse ComponentOf PriorSimply Composite
      ComposedOfMatterAndForm Infinite Eternal HasIntellect HasWill essenceOf esseOf
      hSuffice hMaximal hGenus hCauseMore hUniting hBeing hPreexist hGoodness hPerfections
      hFirstBeing hPrior hNotBoth hKinds hInfinity hEternity hNoComponent hImmaterial hWillFollows
  have hOne : IsTheOneGod σ.IsGod m := by
    intro g hg
    by_cases hSame : g = m
    · exact hSame
    · exact (hm.2 g (hCauseMore g m esse hSame
        (hGenus esse g (hMaximal g hg) m (fun h => hSame h.symm) hm.1))).elim
  exact ⟨m, hfGod, hOne, hAttributes m hfGod⟩

end TruthCore.Results.Case.Catholicism.StrengthConsumers.IdentityWitness
