import TruthCore.Alternatives.McTaggart
import TruthCore.Case.Catholicism.Root
import TruthCore.Case.Catholicism.StageOne.CausalFinitism
import TruthCore.Case.Catholicism.StageOneQuartaVia
import TruthCore.Case.Catholicism.StageTwo
import TruthCore.Causality.FiniteBranching
import TruthCore.Greek.Aristotle.Metaphysics
import TruthCore.Greek.Aristotle.MetaphysicsIX
import TruthCore.Greek.Aristotle.Physics
import TruthCore.Greek.Aristotle.Physics.Typed.Motion
import TruthCore.History.Resurrection
import TruthCore.History.ResurrectionVocabulary
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.InfinityEternity
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.IntellectWill
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question105.Article5
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3QuartaVia
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3SecundaVia
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article1
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article7
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article7Cause
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article8
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question4.Article1
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question4.Article2
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question5.Article1

/-!
First-closure hunt (#497, fourth slice): kernel-checked countermodels.

The floor criteria of #500 admit a premise as `logical` only by proving it
from definitions. Each theorem below interprets the parameters of one
root-path open premise (`corpus.py frontier --reaching-root` at the merge of
#503) so that the premise fails. A proof of the premise from definitions alone
would specialize to that interpretation, so none of the 49 premises closes as
a logical truth. All are zero-axiom except
`finiteImmediatePredecessors_notLogical`, which uses Mathlib's
`Set.infinite_univ` (`propext`, `Classical.choice`, `Quot.sound`, permitted by
`docs/axiom-policy.md` for a Mathlib proof). This is non-entailment from the definitions only: it says
nothing about whether a premise is true, and the interpretations are not
claimed to be faithful to any source.

`opinionGate` certifies the McTaggart chain toward
`STMT-SOMETHING-IS-MOVED-IN-THIS-WORLD`: every other chain member and both
recorded rivals hold while the target fails, so no closure of that premise
from the current chain is possible without `STMT-OPINION-IS-A-MOTION`.
-/

namespace TruthCore.Alternatives.FirstClosure

open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism

/-! ## Root-path premises that are not provable from definitions -/

theorem causeOfQualityInAnotherIsMoreSuch_notLogical :
    ¬ @TruthCore.Greek.Aristotle.Metaphysics.CauseOfQualityInAnotherIsMoreSuchReading Bool Unit
      (fun _ _ _ => True) (fun _ _ _ => False) :=
  fun h => h true false () (by decide) trivial

theorem maximumInGenusCausesAllInGenus_notLogical :
    ¬ @MaximumInGenusCausesAllInGenusReading Bool Unit
      (fun _ _ => True) (fun _ _ _ => False) (fun _ _ _ => False) :=
  fun h => h () true ⟨trivial, fun _ h => h⟩ false (by decide) trivial

theorem maximumInBeingIsFirstBeing_notLogical :
    ¬ @MaximumInBeingIsFirstBeing Bool Unit
      (fun _ _ => True) (fun _ _ _ => False) () (fun _ _ => True) :=
  fun h => absurd (h true ⟨trivial, fun _ h => h⟩ false trivial) (by decide)

theorem potencyIsUnactualizedCapacity_notLogical :
    ¬ @TruthCore.Greek.Aristotle.Metaphysics.PotencyIsUnactualizedCapacityReading Unit Unit
      (fun _ _ => False) (fun _ _ => True) (fun _ _ => False) :=
  fun h => ((h () ()).1 trivial).1

theorem actualityOnlyInsofarAsBeing_notLogical :
    ¬ @ActualityOnlyInsofarAsBeingReading Unit Bool (fun _ r => r = true) false :=
  fun h => absurd (h () true rfl) (by decide)

theorem noComponentIsFirstBeing_notLogical :
    ¬ @NoComponentIsFirstBeingReading Unit (fun _ _ => True) (fun _ _ => False) :=
  fun h => h () () trivial (fun _ h => h.elim)

theorem causeOfBeingCausesEveryPerfection_notLogical :
    ¬ @CauseOfBeingCausesEveryPerfection Unit Bool
      (fun _ _ => True) (fun _ _ r => r = false) false :=
  fun h => absurd (h () () true rfl trivial) (by decide)

theorem finiteImmediatePredecessors_notLogical :
    ¬ @TruthCore.Causality.FiniteBranching.FiniteImmediatePredecessors Nat (fun _ _ => True) :=
  fun h => Set.infinite_univ (α := Nat) (h 0)

theorem wellFoundedPredecessors_notLogical :
    ¬ @TruthCore.Causality.FiniteBranching.WellFoundedPredecessors Unit (fun _ _ => True) :=
  fun h => h.asymmetric () () trivial trivial

theorem noCausalLoops_notLogical :
    ¬ @TruthCore.Case.Catholicism.StageOne.CausalFinitism.NoCausalLoops Unit (fun _ _ => True) :=
  fun h => h () (Relation.TransGen.single trivial)

theorem perSeLinksIncluded_notLogical :
    ¬ @TruthCore.Case.Catholicism.StageOne.CausalFinitism.PerSeLinksIncluded Unit
      (fun _ _ => False) (fun _ _ => True) :=
  fun h => @h () () trivial

theorem movesOnlyAsInAct_notLogical :
    ¬ @MovesOnlyAsInActReading Unit Unit (fun _ _ _ => True) (fun _ _ => False) :=
  fun h => h () () () trivial

theorem godNamesTheFullyDescribedPrinciple_notLogical :
    ¬ @GodNamesTheFullyDescribedPrinciple Unit Unit
      (fun _ _ => True) (fun _ _ _ => False) (fun _ _ _ => True) () (fun _ _ => False)
      (fun _ => False) :=
  fun h => h () ⟨trivial, fun _ h => h⟩ (fun _ _ _ => trivial) (fun _ _ _ _ => trivial)
    (fun _ h => h) (fun _ _ => rfl)

theorem perSeMoverLinkIsPerSeCauseLink_notLogical :
    ¬ @PerSeMoverLinkIsPerSeCauseLinkReading Unit (fun _ _ => True) (fun _ _ => False) :=
  fun h => h () () trivial

theorem asToBeingSoToTruth_notLogical :
    ¬ @TruthCore.Greek.Aristotle.Metaphysics.AsToBeingSoToTruthReading Unit Bool
      (fun _ r => r = true) (fun _ _ _ => False) true false :=
  fun h => absurd ((h.1 ()).1 rfl) (by decide)

theorem gradesHaveAMaximum_notLogical :
    ¬ @GradesByApproachToAMaximumReading Unit Unit (fun _ _ => False) (fun _ _ _ => True) :=
  fun h => (h () ⟨(), (), trivial⟩).elim fun _ hm => hm.1

theorem thingsMoreAndLessGoodTrueNoble_notLogical :
    ¬ @GradesFoundInThingsReading Unit Unit (fun _ _ _ => False) () () () :=
  fun h => h.1.elim fun _ ⟨_, h⟩ => h

theorem secondMoversMoveOnlyAsMoved_notLogical :
    ¬ @SecondMoversMoveOnlyAsMovedReading Bool Unit
      (fun _ _ => True) (fun _ _ _ => True) (fun _ _ => False) :=
  fun h => h true false () (by decide) trivial ⟨(), trivial⟩

theorem beingMovedIsActualizationOfPotency_notLogical :
    ¬ @TruthCore.Greek.Aristotle.Physics.BeingMovedIsActualizationOfPotencyReading Unit Unit
      (fun _ _ => True) (fun _ _ => False) (fun _ _ => False) :=
  fun h => ((h () ()).1 trivial).1

open TruthCore.Greek.Aristotle.Physics.Typed in
theorem everyMotionNaturalOrForced_notLogical :
    ¬ @EveryMotionNaturalOrForcedReading Unit Unit
      (fun _ => True) (fun _ _ => True) (fun _ _ => False) (fun _ _ => False) :=
  fun h => (h () () trivial trivial).elim id id

open TruthCore.Greek.Aristotle.Physics.Typed in
theorem forcedMotionByAnother_notLogical :
    ¬ @ForcedMotionByAnotherReading Unit Unit (fun _ _ => True) (fun _ _ _ => True) :=
  fun h => (h () () trivial).elim fun _ hy => hy.1 rfl

open TruthCore.Greek.Aristotle.Physics.Typed in
theorem naturalMotionSelfOrPassive_notLogical :
    ¬ @NaturalMotionSelfOrPassiveReading Unit Unit
      (fun _ _ => True) (fun _ _ => False) (fun _ _ => False) :=
  fun h => (h () () trivial).elim id id

open TruthCore.Greek.Aristotle.Physics.Typed in
theorem naturalSelfMotionHasAMover_notLogical :
    ¬ @NaturalSelfMotionByAMoverReading Unit Unit
      (fun _ _ => True) (fun _ _ => True) (fun _ _ _ => False) :=
  fun h => (h () () trivial trivial).elim fun _ h => h

open TruthCore.Greek.Aristotle.Physics.Typed in
theorem passiveNaturalMotionByGeneratorOrRemover_notLogical :
    ¬ @PassiveNaturalMotionByGeneratorOrRemoverReading Unit Unit
      (fun _ _ => True) (fun _ _ _ => False) (fun _ _ _ => False) :=
  fun h => (h () () trivial).elim fun _ h => h.elim id id

open TruthCore.Greek.Aristotle.Physics.Typed in
theorem perAccidensMovedPassiveMotionHasPerSeMover_notLogical :
    ¬ @PerAccidensMovedPassiveMotionHasPerSeMoverReading Unit Unit
      (fun _ _ => True) (fun _ _ _ => False) (fun _ _ _ => True) :=
  fun h => (h () () () trivial trivial).elim fun _ h => h

theorem godIsMaximalInBeing_notLogical :
    ¬ @GodIsMaximalInBeing Unit Unit (fun _ => True) (fun _ _ => False) (fun _ _ _ => False) () :=
  fun h => (h () trivial).1

theorem everyCreatedAgentActsAsAppliedToActByGod_notLogical :
    ¬ @CreatedAgentIsAppliedToActByGodReading Bool Unit
      (fun _ _ => False) (fun _ _ _ => True) (fun _ _ _ => True) () (fun b => b = true) :=
  fun h => (h true false rfl (by decide) trivial ⟨true, (), trivial⟩).elim fun _ h => h

theorem actSimplyPriorToPotency_notLogical :
    ¬ @ActSimplyPriorToPotencyReading Unit Unit (fun _ _ => False) (fun _ _ => True) (fun _ _ => True) :=
  fun h => (h () () trivial).elim fun _ h => h.1

open TruthCore.Greek.Aristotle.Physics.Typed in
theorem everyReductionToActIsPhysicalMotion_notLogical :
    ¬ @EveryReductionIsPhysicalMotionReading Unit Unit (fun _ => False) (fun _ _ => True) :=
  fun h => h () () trivial

theorem somethingIsMovedInThisWorld_notLogical :
    ¬ @SomethingIsMovedReading Unit Unit (fun _ _ => False) :=
  fun h => h.elim fun _ ⟨_, h⟩ => h

theorem nothingReducedToActExceptByAMover_notLogical :
    ¬ @ReducedOnlyByAMoverReading Unit Unit (fun _ _ => True) (fun _ _ _ => False) :=
  fun h => (h () () trivial).elim fun _ h => h

theorem compositeHasAUnitingCause_notLogical :
    ¬ @CompositeHasAUnitingCauseReading Unit Unit (fun _ => True) (fun _ _ _ => True) () :=
  fun h => (h () trivial).elim fun _ hc => hc.1 rfl

theorem matterFormAndEsseEssenceAreCompositions_notLogical :
    ¬ @MatterFormAndEsseEssenceAreCompositionsReading Unit Unit
      (fun _ => True) (fun _ => False) (fun _ => ()) (fun _ => ()) :=
  fun h => (h ()).1 trivial

theorem goodnessIsActuality_notLogical :
    ¬ @GoodnessIsActualityReading Unit Unit (fun _ _ => True) (fun _ _ => False) :=
  fun h => (h () ()).1 trivial

theorem perfectionsOfEffectPreexistInCause_notLogical :
    ¬ @PerfectionsOfEffectPreexistInCauseReading Bool Unit
      (fun b _ => b = true) (fun _ _ _ => True) () :=
  fun h => absurd (h false true () trivial rfl) (by decide)

theorem immaterialIsIntellectual_notLogical :
    ¬ @ImmaterialIsIntellectualReading Unit (fun _ => False) (fun _ => False) (fun _ _ => False) :=
  fun h => h () (fun h => h) (fun _ h => h)

theorem immutableIsEternal_notLogical :
    ¬ @ImmutableIsEternalReading Unit Unit (fun _ _ => False) (fun _ => False) :=
  fun h => h () (fun _ h => h)

theorem subsistentBeingIsInfinite_notLogical :
    ¬ @SubsistentBeingIsInfiniteReading Unit Unit (fun _ => ()) (fun _ => ()) (fun _ => False) :=
  fun h => h () rfl

theorem willFollowsIntellect_notLogical :
    ¬ @WillFollowsIntellectReading Unit (fun _ => True) (fun _ => False) :=
  fun h => h () trivial

/-- A case signature with one being and two societies (`true` is the
Catholic Church); each listed predicate is the given constant proposition
and every Creed article is false. -/
def sig (god classical reveals claimed rose founded visible teaching proposes : Prop) :
    Signature where
  Being := Unit
  IsGod := fun _ => god
  HasClassicalAttributes := fun _ => classical
  RevealsRecognizably := fun _ => reveals
  jesus := ()
  ClaimedDivineAuthority := fun _ => claimed
  RoseFromTheDead := fun _ => rose
  Society := Bool
  catholicChurch := true
  Founded := fun _ _ => founded
  VisibleWithAuthority := fun _ => visible
  FoundedAsTeachingAuthority := fun _ _ => teaching
  DefinitivelyProposesAsRevealed := fun _ _ => proposes
  creedOneGodFatherAlmightyCreator := False
  creedOneLordJesusChristOnlyBegottenConsubstantial := False
  creedIncarnateOfSpiritAndVirginMary := False
  creedCrucifiedUnderPilateSufferedBuried := False
  creedRoseOnTheThirdDay := False
  creedAscendedSeatedAtRightHand := False
  creedWillComeToJudgeKingdomWithoutEnd := False
  creedHolySpiritLordGiverOfLife := False
  creedOneHolyCatholicApostolicChurch := False
  creedOneBaptismForForgiveness := False
  creedResurrectionOfTheDead := False
  creedLifeOfTheWorldToCome := False

/-- The stage-4 pilot state over `sig` with every predicate false. -/
def state : TruthCore.History.Resurrection.State where
  core := sig False False False False False False False False False
  reports := fun _ => false
  crucified := false
  diedOnCross := false
  proclaimedBeforeLetter := false
  tombEmpty := false
  experienced := fun _ => false
  sincere := fun _ => false
  believes := fun _ _ => false
  mechanism := .risenEncounter
  bodyRemoved := false
  recovered := false
  godCausesWorld := False
  authorityVindicated := False
  paulEncounterCausedBelief := false
  jamesEncounterCausedBelief := false

theorem classicalAttributesSuffice_notLogical :
    ¬ ClassicalAttributesSuffice (sig False False False False False False False False False)
      (fun _ => True) (fun _ => True) (fun _ => True) (fun _ => True) (fun _ => True)
      (fun _ => True) (fun _ => True) (fun _ => True) (fun _ => True) :=
  fun h => h () trivial trivial trivial trivial trivial trivial trivial trivial trivial

theorem pilotJesusClaims_notLogical : ¬ TruthCore.History.Resurrection.JesusClaims state :=
  fun h => h

theorem pilotRose_notLogical : ¬ TruthCore.History.Resurrection.Rose state :=
  fun h => h

theorem bridgeChristsChurchFoundedByGod_notLogical :
    ¬ BridgeChristsChurchFoundedByGod (sig True True True True True True True False False) :=
  fun h => h () trivial trivial trivial trivial trivial true trivial trivial

theorem bridgeGodFoundedAuthorityProposesOnlyTruth_notLogical :
    ¬ BridgeGodFoundedAuthorityProposesOnlyTruth (sig True True True True True True True True True) :=
  fun h => h () true trivial trivial trivial False trivial

theorem catholicChurchDefinitivelyProposesCreed_notLogical :
    ¬ CatholicChurchDefinitivelyProposesCreed (sig False False False False False False False False False) :=
  fun h => h _ (List.Mem.head _)

theorem christFoundedVisibleChurch_notLogical :
    ¬ ChristFoundedVisibleChurch (sig False False False False False False False False False) :=
  fun h => h.elim fun _ h => h.1

theorem christsChurchIsTheCatholicChurch_notLogical :
    ¬ ChristsChurchIsCatholicChurch (sig False False False False False True True False False) :=
  fun h => Bool.false_ne_true (h false trivial trivial)

theorem jesusClaimedDivineAuthorityAndRose_notLogical :
    ¬ JesusClaimedDivineAuthorityAndRose (sig False False False False False False False False False) :=
  fun h => h.1

theorem revelationPossibleAndRecognizable_notLogical :
    ¬ RevelationPossibleAndRecognizable (sig True False False False False False False False False) :=
  fun h => h () trivial

/-! ## The McTaggart chain needs `STMT-OPINION-IS-A-MOTION` -/

open TruthCore.Alternatives.ActPotencyRegress TruthCore.Alternatives.McTaggart in
/-- Nothing is moved, nothing changes, nothing changes in its A-series
determinations, and the one being opines everything. Then
`STMT-ELEATIC-THESIS-IS-OPINED`, `STMT-MOTION-IS-A-CHANGE`, both commitments
of McTaggart's bundle, and both recorded rivals of
`STMT-SOMETHING-IS-MOVED-IN-THIS-WORLD` (the Eleatic thesis and
`STMT-CHANGE-UNREAL-BUT-APPEARS`) hold, while `STMT-OPINION-IS-A-MOTION` and
the target fail. So no closure of the target from these members exists
without `STMT-OPINION-IS-A-MOTION`. -/
theorem opinionGate :
    let MovedIn : Unit → Unit → Prop := fun _ _ => False
    let Opines : Unit → Prop → Prop := fun _ _ => True
    let Changes : Unit → Prop := fun _ => False
    let ASeriesChanges : Unit → Prop := fun _ => False
    EleaticThesisIsOpinedReading MovedIn Opines ∧
      MotionIsChangeReading MovedIn Changes ∧
      NoASeriesChangeButAppearsReading ASeriesChanges Opines ∧
      AllChangeIsASeriesChangeReading Changes ASeriesChanges ∧
      NothingIsMovedReading MovedIn ∧
      ChangeUnrealButAppearsReading MovedIn Opines ∧
      ¬ OpiningIsBeingMovedReading MovedIn Opines (fun _ => ()) ∧
      ¬ SomethingIsMovedReading MovedIn :=
  ⟨⟨(), trivial⟩, fun _ _ h => h, ⟨fun _ h => h, (), True, trivial⟩, fun _ h => h.elim,
    fun _ _ h => h, ⟨fun _ _ h => h, (), True, trivial⟩, fun h => h () True trivial,
    fun h => h.elim fun _ ⟨_, h⟩ => h⟩

end TruthCore.Alternatives.FirstClosure
