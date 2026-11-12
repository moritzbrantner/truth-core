module

public import TruthCore.Causality.DeiFiliusImmenseIncomprehensible
public import TruthCore.Causality.DeiFiliusLordBlessed
public import TruthCore.Causality.ReceptionLimitation
public import TruthCore.Causality.NecessaryClassicalGodRootControl
public import TruthCore.Case.Catholicism.ClassicalAttributesLocalLogic

/-! The unified Dei Filius route: every typed sense at once

`DeiFiliusLivingNineScope`, `DeiFiliusLordBlessed` and
`DeiFiliusImmenseIncomprehensible` each give the restated sufficiency
(`NineSufficeForDeiFilius`) and the Dei Filius root a second route that types
some of the five primitives and keeps the old bridge for the others. The results
module of this batch composes one route that passes every primitive through its
typed sense and that sense's bridge at once: LIVING_2 (from the nine, through the
operation derivation) with the restricted sense bridge to LIVING_1, LORD_2,
BLESSED_2, IMMENSE_2 and INCOMPREHENSIBLE_2 with their sense bridges. No old
living, lord, blessed, immense or incomprehensible bridge is an input.

It also derives the open bridge `CausedIsNotInfinite` (what has its being caused
by another is not INFINITE_1, after ST I q.7 a.2 and ad 1) from one new explicit
open bridge, `CausedEsseIsReceived` (what has its being caused by another has its
esse received in some principle), and two existing open premises of the
reception-limitation vocabulary: received esse is limited (q.7 a.2, generalized)
and an INFINITE_1 being's esse is not limited (q.7 a.1). The step from an external
cause of esse to received esse, which `DISAMB-ESSE-RECEPTION` keeps apart, is thus
one named premise; it does not pass through `Creature`, whose definition
(`DEF-CREATURE`: ordered to God as principle and cause) is narrower than the
reading the existing premise `CausedInBeingByAnotherIsCreature` gives it.

This module adds that one bridge and no other philosophical vocabulary. It holds the two finite models
(`Control`) that witness the joint satisfiability of each unified route's whole
premise bundle, including the open leaves of the registered derivations of its
nine-statements, together with a being that has the nine. Analyst formulations,
attribution deferred. -/

@[expose] public section

namespace TruthCore.Causality.DeiFiliusUnifiedRoute

open TruthCore.Case.Catholicism
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Causality.DeiFiliusAttributeField
open TruthCore.Causality.DeiFiliusLivingNineScope (HasTheNine NineLiveSomeTime NineOperate)
open TruthCore.Causality.DeiFiliusLivingSelfOperation (PureActLifeAtSomeTimeIsLiving)
open TruthCore.Causality.DeiFiliusOperationFromIntellect
  (IntellectIsCapacityToUnderstand UnderstandingCapacityExercisedOrInPotency
    ExercisedUnderstandingIsImmanentOperation)
open TruthCore.Causality.DeiFiliusLordBlessed
open TruthCore.Causality.DeiFiliusImmenseIncomprehensible
open TruthCore.Causality.SelfOperationLife (SelfOperatingUnmovedLives)
open TruthCore.Causality.ReceptionLimitation (ReceivedEsseIsLimited InfiniteEsseIsUnlimited)
open TruthCore.Causality.NamingVeracityBatch1 (Power InfiniteActHasInfinitePower)

/-- Open bridge: whatever has its being caused by some being distinct from it has
its esse received in some principle (`EsseReceivedIn`, DEF-ESSE-RECEIVED-IN: a
principle standing to it as receiving potency to received act). After ST I q.7
a.2 (the esse of a subsistent created form is received and contracted) and De
ente c.4 (what has esse from another receives it), generalized to everything
caused as to being. It joins the two notions DISAMB-ESSE-RECEPTION keeps apart,
origin from another and reception in a principle, as one explicit premise. It
does not say the principle is the thing's own essence, nor what the principle
really is. SCOPE CONDITION (definition `80dea550`): elements of the domain are
individuated by their act of being, so the divine processions are no instances of
`CausesIn c x esse` with `c ≠ x`; read with them as instances, the bridge would
give the Son received, and so (with `ReceivedEsseIsLimited`) limited, esse. -/
def CausedEsseIsReceived {B R P : Type} (CausesIn : B → B → R → Prop) (esse : R)
    (EsseReceivedIn : B → P → Prop) : Prop :=
  ∀ c x, c ≠ x → CausesIn c x esse → ∃ z, EsseReceivedIn x z

/-! ## Joint satisfiability models -/

namespace Control

/-! ### The sufficiency route, on two beings

`true` has the nine; `false` is a caused intellect: composite (its esse is not its
essence), in potency to understanding and moved in that respect, not infinite,
caused, with received and limited esse. Respects: `false` is esse, `true`
is understanding. -/

/-- Both beings exist; only `true` is in act in understanding. -/
def inAct (x r : Bool) : Prop := x = true ∨ r = false
/-- `false` is in potency to understanding, and to nothing else. -/
def potency (x r : Bool) : Prop := x = false ∧ r = true
/-- `true` causes every perfection of `false`. -/
def causes (c x : Bool) (_ : Bool) : Prop := c = true ∧ x = false
/-- `true` is more in every respect than `false`. -/
def more (_ : Bool) (y x : Bool) : Prop := y = true ∧ x = false
def noComponent (_ _ : Bool) : Prop := False
/-- Every essence is `true`; each being's esse is itself. -/
def essence (_ : Bool) : Bool := true
def esseOf (x : Bool) : Bool := x
def composite (x : Bool) : Prop := x = false
def noMatterForm (_ : Bool) : Prop := False
def isTrue (x : Bool) : Prop := x = true
def isFalse (x : Bool) : Prop := x = false
def yes (_ : Bool) : Prop := True
def no (_ : Bool) : Prop := False
/-- Both beings live at the one time of the frame. -/
def livesAt (_ : Bool) (_ : Unit) : Prop := True
def governs (g _ : Bool) : Prop := g = true
def directs (g _ : Bool) (_ : Unit) : Prop := g = true
/-- Each intellect comprehends itself and nothing else. -/
def selfComprehension : Comprehension Bool := ⟨fun x y => x = y⟩
/-- Both have the capacity to understand, and to nothing else. -/
def canBe (_ r : Bool) : Prop := r = true
/-- The esse of `false` is received in its essence `true`. -/
def received (x z : Bool) : Prop := x = false ∧ z = true

/-- A two-being signature whose GOD_4 is `true`; the other fields are unused
placeholders, not historical or religious assertions. -/
def sig : Signature where
  Being := Bool
  IsGod := isTrue
  HasClassicalAttributes := isTrue
  RevealsRecognizably _ := False
  jesus := false
  ClaimedDivineAuthority _ := False
  RoseFromTheDead _ := False
  Society := Unit
  catholicChurch := ()
  Founded _ _ := False
  VisibleWithAuthority _ := False
  FoundedAsTeachingAuthority _ _ := False
  DefinitivelyProposesAsRevealed _ _ := False
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

/-- One consistent task, which only `true` can do. -/
def power : Power sig where
  Task := Unit
  revealWithSigns := ()
  Consistent _ := True
  CanDo x _ := x = true
  Perfection := Unit
  Requires _ _ := True
  InAct x _ := x = true
  PossibleAct _ := True

/-- Only `true` has each of the five primitives. -/
def prims : Primitives Bool := ⟨isTrue, isTrue, isTrue, isTrue, isTrue⟩

/-- The whole premise bundle of the unified sufficiency route at this
interpretation: its fifteen premises, then the open leaves of the registered
derivations of its nine-statements (operation and life, government,
understanding, and the three reception premises and the finite-intellect bridge
under incomprehensibility), and the derived `CausedIsNotInfinite` itself. -/
def SufficiencyBundle : Prop :=
  NineLiveSomeTime inAct inAct potency causes false isTrue composite isTrue isTrue yes yes
    livesAt ∧
  PureActLifeAtSomeTimeIsLiving potency livesAt prims ∧
  NineAreLordByCauseAndGovernment inAct inAct potency causes false isTrue composite isTrue isTrue
    yes yes governs ∧
  CauseAndGovernorOfAllIsLord inAct causes false governs prims ∧
  NineAreBlessedByUnderstanding inAct inAct potency causes false true isTrue composite isTrue
    isTrue yes yes ∧
  UnderstandingPerfectIsMostBlessed inAct inAct false true yes prims ∧
  NineAreImmenseAsInfiniteCauseOfAll inAct inAct potency causes false isTrue composite isTrue
    isTrue yes yes ∧
  InfiniteCauseOfAllIsImmense inAct causes false isTrue prims ∧
  NineAreIncomprehensibleToCausedIntellects inAct inAct potency causes false isTrue composite
    isTrue isTrue yes yes selfComprehension ∧
  InfiniteUncomprehendedIsIncomprehensible causes false isTrue yes selfComprehension prims ∧
  InfiniteActHasInfinitePower sig isTrue power ∧
  CreatorOfAllIsNoComponent inAct causes false noComponent ∧
  ExcessInBeingIsExcessInAct inAct more false ∧
  GoodnessIsActualityReading inAct inAct ∧
  MatterFormAndEsseEssenceAreCompositionsReading noMatterForm composite essence esseOf ∧
  -- leaves under the nine-statements
  IntellectIsCapacityToUnderstand yes canBe true ∧
  UnderstandingCapacityExercisedOrInPotency inAct potency canBe true ∧
  ExercisedUnderstandingIsImmanentOperation inAct canBe true isTrue ∧
  SelfOperatingUnmovedLives isTrue potency livesAt ∧
  MovedOnlyAsInPotencyReading potency potency ∧
  UniversalIntellectualCauseDirectsAll inAct causes false yes yes directs ∧
  DirectingToAnEndIsGoverningReading directs governs ∧
  CausedIsNotInfinite causes false isTrue ∧
  CausedEsseIsReceived causes false received ∧
  ReceivedEsseIsLimited isFalse received ∧
  InfiniteEsseIsUnlimited isFalse isTrue ∧
  FiniteIntellectDoesNotComprehendInfinite isTrue yes selfComprehension

/-- Sufficiency model: the whole bundle holds, `true` has the nine and every
Dei Filius attribute, and the old living bridge (whatever has intellect is
LIVING_1) fails, since `false` has intellect and is not LIVING_1. -/
def SufficiencyModel : Prop :=
  SufficiencyBundle ∧
  HasTheNine inAct inAct potency causes false isTrue composite isTrue isTrue yes yes true ∧
  DeiFiliusAttributes sig inAct inAct potency causes false more noComponent composite
    noMatterForm isTrue isTrue yes yes power prims true ∧
  ¬ IntellectualIsLiving yes prims

/-! ### The root route, on the four roles of the full25 fixture

The exact act, cause, grade, modal, part, priority, cognitive, potency and
eternity dictionaries of `NecessaryClassicalGodRootControl` (and through it
`RootPositiveIntellectWillControl`), with one change: every essence is
`source`, so every being other than `source` has esse distinct from essence, is
composite and is not INFINITE_1. In the old fixture `supporter` and `recipient`
have esse equal to essence and are caused by `source`, so `CausedIsNotInfinite`
fails there (part of `Controls`). Because the old act dictionary is everywhere
true and potency empty, every role is pure act and universally perfect; the
model witnesses joint satisfiability only. -/

open TruthCore.Causality.RootPositiveIntellectWillControl
  (model profile prior component matterForm intellect will)
open TruthCore.Causality.NecessaryClassicalGodRootControl (signature god eternal)

/-- Every essence is `source`. -/
def rootEssence (_ : TransferRole) : TransferRole := .source
/-- The old profile with the new essence map. -/
def rootProfile : PrimaPars.Question3.Article4.Profile TransferRole TransferRole Bool :=
  { profile with essenceOf := rootEssence }
def rootComposite (x : TransferRole) : Prop := x ≠ .source
def rootInfinite (x : TransferRole) : Prop := x = .source
def rootPotency (_ : TransferRole) (_ : Bool) : Prop := False
def isSource (x : TransferRole) : Prop := x = .source
def notSource (x : TransferRole) : Prop := x ≠ .source
def rootLivesAt (x : TransferRole) (_ : Unit) : Prop := intellect x
def rootGoverns (g _ : TransferRole) : Prop := g = .source
def rootDirects (g _ : TransferRole) (_ : Unit) : Prop := g = .source
def rootComprehension : Comprehension TransferRole := ⟨fun x y => x = y⟩
def rootCanBe (x : TransferRole) (_ : Bool) : Prop := intellect x
def rootReceived (x z : TransferRole) : Prop := x ≠ .source ∧ z = .source
def rootNoMoved (_ : TransferRole) (_ : Bool) : Prop := False

/-- One consistent task, which only `source` can do. -/
def rootPower : Power signature where
  Task := Unit
  revealWithSigns := ()
  Consistent _ := True
  CanDo x _ := x = .source
  Perfection := Unit
  Requires _ _ := True
  InAct x _ := x = .source
  PossibleAct _ := True

/-- `source` is immense, incomprehensible and lord; both intellects live and are
most blessed (on the all-true act dictionary both are BLESSED_2). -/
def rootPrims : Primitives TransferRole := ⟨intellect, isSource, isSource, isSource, intellect⟩

/-- The whole premise bundle of the unified root route at this interpretation,
given excluded middle (itself a premise): the twenty-one other spine-root
premises, the eleven Dei Filius premises, then the open leaves of the registered
derivations of its nine-statements and the derived `CausedIsNotInfinite`. -/
def RootBundle : Prop :=
  TruthCore.Causality.NecessaryConcreteUnderived.NecessaryConcreteUnderivedAt model false ∧
  MaximumInBeingCausesAllBeingsReading rootProfile.InAct (transferMore true)
    rootProfile.CausesIn rootProfile.esse ∧
  TruthCore.Causality.ExistenceActuality.ExistingInActAt model.ontic rootProfile.InAct
    rootProfile.esse false ∧
  TruthCore.Causality.NecessaryConcreteRouteBridge.EsseCauseIsActualConcreteGround model false
    rootProfile.CausesIn rootProfile.esse ∧
  TruthCore.Causality.DirectEsseRootUniquenessAtBeing.GradesToMaximumAtBeing rootProfile.InAct
    (transferMore true) rootProfile.esse ∧
  ActualityOnlyInsofarAsBeingReading rootProfile.InAct rootProfile.esse ∧
  PerfectionsOfEffectPreexistInCauseReading rootProfile.InAct rootProfile.CausesIn
    rootProfile.esse ∧
  GoodnessIsActualityReading transferAct rootProfile.InAct ∧
  UniversalCauseTransfersPerfections rootProfile.InAct rootProfile.CausesIn rootProfile.esse ∧
  CompositeHasAUnitingCauseReading rootComposite rootProfile.CausesIn rootProfile.esse ∧
  MatterFormAndEsseEssenceAreCompositionsReading matterForm rootComposite rootProfile.essenceOf
    rootProfile.esseOf ∧
  TruthCore.Causality.NecessaryConcreteRouteBridge.SimplyPriorIsActualConcreteGround model false
    prior ∧
  NoComponentIsFirstBeingReading component prior ∧
  ImmaterialIsIntellectualReading matterForm intellect component ∧
  WillFollowsIntellectReading intellect will ∧
  TruthCore.Case.Catholicism.ClassicalAttributesLocalLogic.IndependentPriority rootProfile.InAct
    rootPotency prior ∧
  NotActAndPotencyInSameRespectReading rootProfile.InAct rootPotency ∧
  SubsistentBeingIsInfiniteReading rootProfile.essenceOf rootProfile.esseOf rootInfinite ∧
  ImmutableIsEternalReading rootPotency eternal ∧
  GodNamesTheFullyDescribedPrinciple
    rootProfile.InAct (transferMore true) rootProfile.CausesIn rootProfile.esse component
    signature.IsGod ∧
  GodIsMaximalInBeing signature.IsGod
    rootProfile.InAct (transferMore true) rootProfile.esse ∧
  -- the Dei Filius premises
  NineLiveSomeTime rootProfile.InAct transferAct rootPotency rootProfile.CausesIn rootProfile.esse
    signature.IsGod rootComposite rootInfinite eternal intellect will rootLivesAt ∧
  PureActLifeAtSomeTimeIsLiving rootPotency rootLivesAt rootPrims ∧
  NineAreLordByCauseAndGovernment rootProfile.InAct transferAct rootPotency rootProfile.CausesIn
    rootProfile.esse signature.IsGod rootComposite rootInfinite eternal intellect will
    rootGoverns ∧
  CauseAndGovernorOfAllIsLord rootProfile.InAct rootProfile.CausesIn rootProfile.esse rootGoverns
    rootPrims ∧
  NineAreBlessedByUnderstanding rootProfile.InAct transferAct rootPotency rootProfile.CausesIn
    rootProfile.esse true signature.IsGod rootComposite rootInfinite eternal intellect will ∧
  UnderstandingPerfectIsMostBlessed rootProfile.InAct transferAct rootProfile.esse true intellect
    rootPrims ∧
  NineAreImmenseAsInfiniteCauseOfAll rootProfile.InAct transferAct rootPotency
    rootProfile.CausesIn rootProfile.esse signature.IsGod rootComposite rootInfinite eternal
    intellect will ∧
  InfiniteCauseOfAllIsImmense rootProfile.InAct rootProfile.CausesIn rootProfile.esse
    rootInfinite rootPrims ∧
  NineAreIncomprehensibleToCausedIntellects rootProfile.InAct transferAct rootPotency
    rootProfile.CausesIn rootProfile.esse signature.IsGod rootComposite rootInfinite eternal
    intellect will rootComprehension ∧
  InfiniteUncomprehendedIsIncomprehensible rootProfile.CausesIn rootProfile.esse rootInfinite
    intellect rootComprehension rootPrims ∧
  InfiniteActHasInfinitePower signature rootInfinite rootPower ∧
  -- leaves under the nine-statements
  IntellectIsCapacityToUnderstand intellect rootCanBe true ∧
  UnderstandingCapacityExercisedOrInPotency rootProfile.InAct rootPotency rootCanBe true ∧
  ExercisedUnderstandingIsImmanentOperation rootProfile.InAct rootCanBe true intellect ∧
  SelfOperatingUnmovedLives intellect rootNoMoved rootLivesAt ∧
  MovedOnlyAsInPotencyReading rootNoMoved rootPotency ∧
  UniversalIntellectualCauseDirectsAll rootProfile.InAct rootProfile.CausesIn rootProfile.esse
    intellect will rootDirects ∧
  DirectingToAnEndIsGoverningReading rootDirects rootGoverns ∧
  CausedIsNotInfinite rootProfile.CausesIn rootProfile.esse rootInfinite ∧
  CausedEsseIsReceived rootProfile.CausesIn rootProfile.esse rootReceived ∧
  ReceivedEsseIsLimited notSource rootReceived ∧
  InfiniteEsseIsUnlimited notSource rootInfinite ∧
  FiniteIntellectDoesNotComprehendInfinite rootInfinite intellect rootComprehension

/-- Root model: given excluded middle, the whole bundle holds and the selected
root is `source` with every Dei Filius attribute. -/
def RootModel : Prop :=
  TruthCore.Logic.ExcludedMiddle →
    RootBundle ∧
    TruthCore.Causality.DeiFiliusAttributeField.NecessaryDeiFiliusGodRootAt signature model false
      rootProfile transferAct rootPotency (transferMore true) prior component rootComposite
      matterForm rootInfinite eternal intellect will rootPower rootPrims

/-- The controls: (1) the sufficiency model; (2) the root model; (3) in the old
full25 fixture, whose `Infinite` is esse equal to essence, `CausedIsNotInfinite`
fails (`supporter` is caused by `source` and has esse equal to essence), which is
why the root model changes the essence map. Statements about these
interpretations only. -/
def Controls : Prop :=
  SufficiencyModel ∧ RootModel ∧
  ¬ CausedIsNotInfinite profile.CausesIn profile.esse
    TruthCore.Causality.NecessaryClassicalGodRootControl.infinite

end Control

end TruthCore.Causality.DeiFiliusUnifiedRoute
