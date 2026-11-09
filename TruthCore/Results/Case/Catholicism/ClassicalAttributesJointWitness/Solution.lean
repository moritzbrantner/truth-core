module
public import TruthCore.Case.Catholicism.ClassicalAttributesJointWitness
@[expose] public section
set_option synthInstance.maxSize 2048
namespace TruthCore.Results.Case.Catholicism.ClassicalAttributesJointWitness
open TruthCore.Case.Catholicism.ClassicalAttributesJointWitness
open TruthCore.Case.Catholicism
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Greek.Aristotle.Metaphysics

private instance boolForall (p : Bool → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  decidable_of_iff (p false ∧ p true) Bool.forall_bool.symm
private instance boolExists (p : Bool → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  decidable_of_iff (p false ∨ p true) Bool.exists_bool.symm

theorem certificate : ExactBoundary := by
  constructor
  · intro h
    exact h.1.2.2.2.2.1
  · intro hEM
    constructor
    · unfold AllPremises
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals first
        | exact hEM
        | (dsimp only [
          Premise0, Premise1, Premise2, Premise3, Premise4,
          Premise5, Premise6, Premise7, Premise8, Premise9,
          Premise10, Premise11, Premise12, Premise13, Premise14,
          Premise15, Premise16, Premise17, Premise18, CausesEveryPerfectionOfOthers,
          ClassicalAttributesSuffice, IsSimple, IsPerfect, IsSupremelyGood, IsTheOneGod,
          IsImmutable, GodIsMaximalInBeing, MaximumInGenusCausesAllInGenusReading, IsMaximumIn, CausesAllInGenus,
          CauseOfQualityInAnotherIsMoreSuchReading, CompositeHasAUnitingCauseReading, ActualityOnlyInsofarAsBeingReading, PerfectionsOfEffectPreexistInCauseReading, GoodnessIsActualityReading,
          CauseOfBeingCausesEveryPerfection, MaximumInBeingIsFirstBeing, IsFirstBeing, ActSimplyPriorToPotencyReading, NotActAndPotencyInSameRespectReading,
          MatterFormAndEsseEssenceAreCompositionsReading, SubsistentBeingIsInfiniteReading, ImmutableIsEternalReading, NoComponentIsFirstBeingReading, ImmaterialIsIntellectualReading,
          WillFollowsIntellectReading, PureAct, InAct, InPotency, GoodIn,
          MoreIn, CausesIn, ComponentOf, PriorSimply, Composite,
          ComposedOfMatterAndForm, Infinite, Eternal, HasIntellect, HasWill,
          essenceOf, esseOf, esse, σ, Nonvacuity]; decide)
    · dsimp only [Nonvacuity, σ, InAct, InPotency, CausesIn, Composite, ComponentOf,
        PriorSimply, essenceOf, esseOf, esse]
      all_goals decide
end TruthCore.Results.Case.Catholicism.ClassicalAttributesJointWitness
