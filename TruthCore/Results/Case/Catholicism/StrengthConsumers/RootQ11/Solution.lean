module

public import TruthCore.Results.Case.Catholicism.FromPrimaViaWithQ11Uniqueness.Solution
public import TruthCore.Results.Case.Catholicism.StrengthConsumers.Q11Witness.Solution

@[expose] public section

namespace TruthCore.Results.Case.Catholicism.StrengthConsumers.RootQ11
open TruthCore.Case.Catholicism
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Greek.Aristotle.Metaphysics (CauseOfQualityInAnotherIsMoreSuchReading)

/-- Analyst composition audit: the same conclusion from the displayed reduced
bundle. The Fourth-Way maximum supplies the witness directly. The frozen
legacy theorem remains unchanged; no premise truth or global minimality follows. -/
theorem catholicismQ11WithoutMotion (σ : Signature) {Respect : Type} {Principle : Type}
    (InPotency InAct GoodIn : σ.Being → Respect → Prop)
    (MoreIn : Respect → σ.Being → σ.Being → Prop)
    (CausesIn : σ.Being → σ.Being → Respect → Prop)
    (bonum verum nobile esse : Respect)
    (ComponentOf PriorSimply : σ.Being → σ.Being → Prop)
    (Composite ComposedOfMatterAndForm Infinite Eternal HasIntellect HasWill : σ.Being → Prop)
    (essenceOf esseOf suppositumOf : σ.Being → Principle) (deity : Principle)
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
    (hIndividual : IndividuatingBasisIsIncommunicableReading suppositumOf)
    (hNature : GodSuppositumIsNatureReading σ.IsGod suppositumOf essenceOf)
    (hCommon : ProperGodInstancesHaveCommonNatureReading σ.IsGod essenceOf deity)
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
  have hWitness := TruthCore.Results.Case.Catholicism.StrengthConsumers.Q11Witness.uniqueClassicalGodQ11WithoutMotion
    σ InPotency InAct GoodIn MoreIn CausesIn bonum verum nobile esse
    ComponentOf PriorSimply Composite ComposedOfMatterAndForm Infinite Eternal HasIntellect HasWill
    essenceOf esseOf suppositumOf deity hNotBoth
    hGrades hApproach hTrue hGenus hBeing hCauseMore hEM hPerfections hNoComponent hFirstBeing
    hFull hSuffice hIndividual hNature hCommon hUniting hPreexist hGoodness hPrior hKinds hInfinity hEternity
    hImmaterial hWillFollows
  obtain ⟨g, hg, hOne, hAttributes⟩ := hWitness
  have hAllAttributes : GodHasClassicalAttributes σ := by
    intro other hOther
    have hSame : other = g := hOne other hOther
    exact hSame.symm ▸ hAttributes
  -- Consume the original skeleton theorem; no church/Creed deduction is restated.
  exact TruthCore.Results.Case.Catholicism.Skeleton.catholicismSkeleton σ ⟨g, hg⟩
    hAllAttributes hRevelation hJesus hFounded hCatholic hDivineFounding hOnlyTruth hProposes
end TruthCore.Results.Case.Catholicism.StrengthConsumers.RootQ11
