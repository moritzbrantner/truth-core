module

public import TruthCore.Causality.SpineRivalsAttributes

/-! Finite tests of the rivals of the stage-two attribute premises. Each lemma
checks one interpretation of `TruthCore.Causality.SpineRivalsAttributes.Control`:
the rival holds, every other premise of the named consuming theorem holds, and
that theorem's conclusion fails. Model claims concern these interpretations
only. -/

@[expose] public section

namespace TruthCore.Results.Causality.SpineRivalsAttributes

open TruthCore.Causality.SpineRivalsAttributes
open TruthCore.Causality.SpineRivalsAttributes.Control
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism
open TruthCore.Alternatives.ActPotencyRegress
open TruthCore.Alternatives.FideismReference
open TruthCore.Alternatives.NameApplicationTransfer
open TruthCore.Causality.CausalMapsBatch1
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryRootFork
open TruthCore.Causality.NecessaryFirstBeing
open TruthCore.Causality.NecessaryFirstAttributes
open TruthCore.Causality.Round2ExistenceAct
open TruthCore.Causality.ExistenceActuality (ExistingInActAt)
open TruthCore.Causality.PureActThisness (FirstMoverHasEveryPureDetermination)
open TruthCore.Causality.WholePowerPerfection (InfiniteHasEveryPurePerfection)
open TruthCore.Greek.Aristotle.Metaphysics (CauseOfQualityInAnotherIsMoreSuchReading)
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt)

theorem actualityWithoutBeing_holds : actualityWithoutBeing.Holds :=
  ⟨⟨(), true, rfl, fun h => Bool.noConfusion h⟩,
   fun _ _ => ⟨true, rfl⟩,
   fun h => Bool.noConfusion (h () trivial)⟩

theorem emergentPerfection_holds : emergentPerfection.Holds := by
  unfold emergentPerfection.Holds EmergentPerfectionReading CausedPerfectionIsHad
    CauseOfBeingHasWhatItGives
  refine ⟨?_, ?_, ?_⟩ <;> decide

theorem actualityWithoutGoodness_holds : actualityWithoutGoodness.Holds := by
  unfold actualityWithoutGoodness.Holds ActualityNotSufficientForGoodnessReading
    GodIsMaximalInBeing MaximumInGenusCausesAllInGenusReading
    ActualityOnlyInsofarAsBeingReading CauseOfBeingCausesEveryPerfection
    GodIsSupremelyGood IsSupremelyGood CausesEveryPerfectionOfOthers IsMaximumIn
    CausesAllInGenus
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem uncausedComposite_holds : uncausedComposite.Holds := by
  unfold uncausedComposite.Holds UncausedCompositeReading GodIsMaximalInBeing
    CauseOfQualityInAnotherIsMoreSuchReading GodIsSimple IsSimple IsMaximumIn
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

theorem differenceWithoutComposition_holds : differenceWithoutComposition.Holds := by
  unfold differenceWithoutComposition.Holds
    EsseEssenceDifferenceWithoutCompositionReading NoBodyMovesUnlessMovedReading
    FirstUnmovedMoverIsFirstBeing CompositePosteriorToComponentsReading
    CompositeHasComponentOtherThanItselfReading FirstUnmovedMoverIsSimpleReading
    IsFirstUnmovedMover IsFirstBeing
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem firstBeingComponent_holds : firstBeingComponent.Holds := by
  unfold firstBeingComponent.Holds FirstBeingIsAComponentReading
    NecessaryActualFirstPureActAt CompositePosteriorToComponentsReading
    CompositeHasComponentOtherThanItselfReading NecessaryFirstAttributesAt
    ActualRoot ActualConcrete NecessaryAt IsFirstBeing PureAct RemoteFromAll
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · decide
  · exact ⟨true, ⟨⟨trivial, trivial⟩, fun y h => h.2.2⟩, fun _ _ => trivial,
      by decide, fun _ h => h⟩
  · decide
  · decide
  · rintro ⟨n, -, -, hFirst, -, -, hRemote⟩
    cases n with
    | false => exact Bool.noConfusion (hFirst true ⟨rfl, rfl⟩)
    | true => exact hRemote false ⟨rfl, rfl⟩

theorem materialIntellect_holds : materialIntellect.Holds := by
  unfold materialIntellect.Holds IntellectOnlyInMaterialCompositesReading
    GodIsMaximalInBeing CompositeHasAUnitingCauseReading
    CauseOfQualityInAnotherIsMoreSuchReading
    MatterFormAndEsseEssenceAreCompositionsReading NoComponentIsFirstBeingReading
    MaximumInBeingIsFirstBeing GodHasIntellect IsMaximumIn IsFirstBeing
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem intellectWithoutWill_holds : intellectWithoutWill.Holds := by
  unfold intellectWithoutWill.Holds IntellectWithoutWillReading
    GodIsMaximalInBeing CompositeHasAUnitingCauseReading
    CauseOfQualityInAnotherIsMoreSuchReading
    MatterFormAndEsseEssenceAreCompositionsReading NoComponentIsFirstBeingReading
    MaximumInBeingIsFirstBeing ImmaterialIsIntellectualReading GodHasWill
    IsMaximumIn IsFirstBeing
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem potencyPrior_holds : potencyPrior.Holds := by
  unfold potencyPrior.Holds PotencyPriorToActReading
    NotActAndPotencyInSameRespectReading FirstBeingIsInNoWayInPotencyReading
    IsFirstBeing PureAct
  refine ⟨?_, ?_, ?_⟩ <;> decide

theorem actAndPotency_holds : actAndPotency.Holds := by
  unfold actAndPotency.Holds InActAndPotencyInSameRespectReading
    ActSimplyPriorToPotencyReading FirstBeingIsInNoWayInPotencyReading
    IsFirstBeing PureAct
  refine ⟨?_, ?_, ?_⟩ <;> decide

theorem finiteSubsistent_holds : finiteSubsistent.Holds := by
  unfold finiteSubsistent.Holds FiniteSubsistentBeingReading
    FirstUnmovedMoverIsSimpleReading InfiniteHasEveryPurePerfection
    FirstMoverHasEveryPureDetermination IsFirstUnmovedMover
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

theorem immutableInTime_holds : immutableInTime.Holds := by
  unfold immutableInTime.Holds ImmutableWithoutEternityReading GodIsMaximalInBeing
    MaximumInBeingIsFirstBeing ActSimplyPriorToPotencyReading
    NotActAndPotencyInSameRespectReading GodIsEternal IsMaximumIn IsFirstBeing
    PureAct
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem namingFails_holds : namingFails.Holds := by
  have hDesc : FullDescriptorExists namingFails.InAct namingFails.MoreIn
      namingFails.CausesIn () namingFails.ComponentOf :=
    ⟨(), ⟨trivial, fun _ h => h⟩, fun x hne _ => (hne rfl).elim,
      fun x _ hne _ => (hne rfl).elim, fun _ h => h, fun _ _ => rfl⟩
  obtain ⟨m, hMax, hAll, hEvery, hRemote, hUnique⟩ := hDesc
  exact ⟨fun hLeaf => hLeaf m hMax hAll hEvery hRemote hUnique,
    fun _ h => h, fun _ h => h.elim, ⟨m, hMax, hAll, hEvery, hRemote, hUnique⟩,
    fun hEx => hEx m hMax hAll hEvery hRemote hUnique⟩

theorem attributesFallShort_holds : attributesFallShort.Holds := by
  unfold attributesFallShort.Holds ClassicalAttributesFallShort
  refine ⟨⟨(), fun h => h, fun _ _ h => h, ⟨trivial, fun x _ hne _ => (hne rfl).elim⟩,
      fun _ _ => rfl, trivial, trivial, trivial, trivial, trivial, fun h => h⟩,
    fun _ _ => ⟨trivial, fun _ h => h⟩, fun _ _ _ x hne _ => (hne rfl).elim,
    fun _ _ _ _ h => h.elim, fun _ h => h.elim, fun _ _ h => h, fun _ _ _ h _ => h.elim,
    fun _ _ => Iff.rfl, fun _ _ _ h _ => h.elim, fun _ _ => trivial, fun _ _ => trivial,
    fun _ _ => trivial, fun _ _ => trivial, fun _ _ => trivial,
    fun h => h () trivial⟩

/-- The fourteen finite tests. -/
theorem controls : TruthCore.Causality.SpineRivalsAttributes.Control.Certificate :=
  ⟨actualityWithoutBeing_holds, emergentPerfection_holds,
   actualityWithoutGoodness_holds, uncausedComposite_holds,
   differenceWithoutComposition_holds, firstBeingComponent_holds,
   materialIntellect_holds, intellectWithoutWill_holds, potencyPrior_holds,
   actAndPotency_holds, finiteSubsistent_holds, immutableInTime_holds,
   namingFails_holds, attributesFallShort_holds⟩

end TruthCore.Results.Causality.SpineRivalsAttributes
