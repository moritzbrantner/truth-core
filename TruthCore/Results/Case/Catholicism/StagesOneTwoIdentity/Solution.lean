import TruthCore.Results.Case.Catholicism.StageTwo.ClassicalAttributesIdentity.Solution
import TruthCore.Results.Aquinas.SummaTheologiae.FirstMoverIsMaximeEnsIdentity.Solution
import TruthCore.Results.Aquinas.SummaTheologiae.MaximeEnsIsGodViaFullDescriptionIdentity.Solution
import TruthCore.Case.Catholicism.StagesOneTwo
import TruthCore.Results.Case.Catholicism.StageOneViaFullDescription.Solution
import TruthCore.Results.Aquinas.SummaTheologiae.PrimaVia.Solution
import TruthCore.Results.Case.Catholicism.StageTwo.ClassicalAttributesAll.Solution
namespace TruthCore.Results.Case.Catholicism.StagesOneTwoIdentity
open TruthCore.Case.Catholicism
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Greek.Aristotle.Metaphysics (CauseOfQualityInAnotherIsMoreSuchReading)

/-- Separate sufficient equality-decision interface. All nonlogical premises remain open.
No existence follows from naming or identifying supplied witnesses. No necessity,
minimality, strict-strength or philosophical-discharge claim. The historical
end, where present, retains the existing structural transcription. -/
theorem uniqueClassicalGodExists (σ : Signature) {Respect : Type} {Principle : Type}
    [DecidableEq σ.Being] [DecidableEq Principle]
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
    TruthCore.Results.Aquinas.SummaTheologiae.MaximeEnsIsGodViaFullDescriptionIdentity.maximeEnsIsGodViaFullDescription
      InAct MoreIn CausesIn esse ComponentOf PriorSimply σ.IsGod hGenus hCauseMore hBeing
      hPerfections hNoComponent hFirstBeing hFull
  have hSame := TruthCore.Results.Aquinas.SummaTheologiae.FirstMoverIsMaximeEnsIdentity.firstMoverIsMaximeEns
    MovedIn MovesIn InAct MoreIn CausesIn esse σ.IsGod hGenus hAct hBeing hNamed hApplied
    f hf m hm
  have hfMax : IsMaximumIn InAct MoreIn esse f := hSame.symm ▸ hm
  have hfGod : σ.IsGod f := hNamed f hfMax
  -- The attribute interface matches the retained original hMaximal premise.
  -- It is applied at f, with σ.IsGod unchanged throughout.
  have hAttributes :=
    TruthCore.Results.Case.Catholicism.StageTwo.ClassicalAttributesIdentity.godHasClassicalAttributes
      σ InPotency InAct GoodIn MoreIn CausesIn esse ComponentOf PriorSimply Composite
      ComposedOfMatterAndForm Infinite Eternal HasIntellect HasWill essenceOf esseOf
      hSuffice hMaximal hGenus hCauseMore hUniting hBeing hPreexist hGoodness hPerfections
      hFirstBeing hPrior hNotBoth hKinds hInfinity hEternity hNoComponent hImmaterial hWillFollows
  have hOne : IsTheOneGod σ.IsGod f := by
    intro g hg
    exact (TruthCore.Results.Aquinas.SummaTheologiae.FirstMoverIsMaximeEnsIdentity.firstMoverIsMaximeEns
      MovedIn MovesIn InAct MoreIn CausesIn esse σ.IsGod hGenus hAct hBeing hNamed hApplied
      f hf g (hMaximal g hg)).symm
  exact ⟨f, hfGod, hOne, hAttributes f hfGod⟩

end TruthCore.Results.Case.Catholicism.StagesOneTwoIdentity
