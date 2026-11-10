module

public import TruthCore.Alternatives.ActPotencyRegress
public import TruthCore.Alternatives.NameApplicationTransfer
public import TruthCore.Case.Catholicism.StageOneBridges
public import TruthCore.Case.Catholicism.StageTwo
public import TruthCore.Causality.CausalMapsBatch1
public import TruthCore.Causality.NecessaryFirstAttributes
public import TruthCore.Causality.Round2ExistenceAct
public import TruthCore.Causality.WholePowerPerfection
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.FirstMoverAttributes
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.InfinityEternity
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.IntellectWill
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article7Cause
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question5.Article1

/-! Rivals of the stage-two attribute premises, and one finite test for each

Analyst formulations, attribution deferred. Stage two of the modal spine to
`STMT-GOD-EXISTS` takes a necessary concrete individual to God through fourteen
premises about act and potency, composition, perfection, goodness, infinity,
eternity, intellect and will, the name "God" and the sufficiency of the
classical attributes. Four of them already had a recorded rival
(`TruthCore.Alternatives.ActPotencyRegress`,
`TruthCore.Alternatives.NameApplicationTransfer`). This module states one rival
for each of the other ten, on the same carrier and the same predicates as the
premise it rivals, and gives one finite interpretation per premise in which the
rival holds together with every other premise of that premise's smallest
verified consuming theorem while the theorem's conclusion fails.

No new vocabulary is introduced: every rival is stated in the parameters of its
premise. Each rival is a position with a replacement account, named in its
doc comment as "motivated by"; no author is attributed the formal statement.
Each doc comment says whether the rival is the exact negation of its premise or
stronger. A finite interpretation shows joint satisfiability under the stated
assignments only. It does not show that the rival is true, that the premise is
false, or that no other premise of the route excludes the rival.
-/

@[expose] public section

namespace TruthCore.Causality.SpineRivalsAttributes

open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism

universe u v w

/-! ## Rivals -/

/-- Rival to `PerfectionsOfEffectPreexistInCauseReading`, motivated by strong
emergence (and by Hume's "anything may produce anything"): some thing whose
being is caused has a perfection that none of the causes of its being has.

Ordinary meaning: wholes get features their producers lack. The standard example
is life or consciousness arising from causes that are neither alive nor
conscious. It is not the claim that the perfection is uncaused, and it does not
deny that the thing has a cause of its being: the second conjunct requires one.
The replacement account is that the novel perfection arises with the effect's
organization and is not found, formally or eminently, in what causes it to be.

Strictly stronger than the negation of the premise: the negation needs one
cause of being that lacks the perfection, this needs every cause of that
thing's being to lack it. -/
def EmergentPerfectionReading {Being : Sort u} {Respect : Sort v}
    (InAct : Being → Respect → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect) : Prop :=
  ∃ x r, InAct x r ∧ (∃ c, CausesIn c x esse) ∧ ∀ c, CausesIn c x esse → ¬ InAct c r

/-- Rival to `GoodnessIsActualityReading`, motivated by the fact/value gap
(Hume's is/ought, Moore's open question) and by the objection to the privation
account that some actualities are bad: being good in a perfection requires
actually having it, but actually having a perfection does not suffice for being
good in it.

Ordinary meaning: value is a further matter than actuality. The standard
example is an actual, fully exercised capacity for cruelty: it is really had and
is not thereby good. It is not the denial that goodness presupposes actuality
(the first conjunct keeps that half of the premise), and it is not nihilism
about value. The replacement account is that goodness is a further feature that
only some actualities have.

Strictly stronger than the negation of the premise: the negation of the
biconditional allows either direction to fail, this keeps the left-to-right
direction and denies only the right-to-left one. -/
def ActualityNotSufficientForGoodnessReading {Being : Sort u} {Perfection : Sort v}
    (GoodIn Has : Being → Perfection → Prop) : Prop :=
  (∀ x p, GoodIn x p → Has x p) ∧ ∃ x p, Has x p ∧ ¬ GoodIn x p

/-- Rival to `CompositeHasAUnitingCauseReading`, motivated by brute composition
and by accounts of a composite necessary being (a God with really distinct
attributes, or a necessary bundle whose members cannot come apart): some
composite has no cause of its being at all.

Ordinary meaning: some unities of diverse things need no unifier. The proposed
example is a being whose distinct attributes necessarily go together; a weaker
one is any composite whose composition is a brute fact. It is not the claim that
no composite has a cause, and it is not self-causation: the composite is denied
every cause of its being, itself included. The replacement account is that the
members cohere of themselves, by necessity or as a brute fact.

Strictly stronger than the negation of the premise: the negation allows a
composite whose only cause of being is itself, this allows none. -/
def UncausedCompositeReading {Being : Sort u} {Respect : Sort v}
    (Composite : Being → Prop) (CausesIn : Being → Being → Respect → Prop)
    (esse : Respect) : Prop :=
  ∃ x, Composite x ∧ ∀ c, ¬ CausesIn c x esse

/-- Rival to `MatterFormAndEsseEssenceAreCompositionsReading`, motivated by
Scotus's formal distinction and by the view that essence and existence differ
without being two parts (Suárez's distinction of reason is the further step of
denying the difference itself, which this carrier cannot express): composition
of matter and form is composition, but something whose act of being is other
than its essence is not composite.

Ordinary meaning: not every difference within a thing is a part-whole
structure. The standard example is a created pure spirit: its essence is not
its existence, yet it has no parts. It is not the denial that matter and form
compose (the first conjunct keeps that half of the premise), and it is not the
claim that esse and essence are identical in that thing. The replacement account
is that the two differ as formalities or aspects of one simple reality.

Strictly stronger than the negation of the premise: the negation allows either
inclusion to fail, this keeps the matter-form inclusion and denies only the
esse-essence one. -/
def EsseEssenceDifferenceWithoutCompositionReading {Being : Sort u}
    {Principle : Sort w}
    (ComposedOfMatterAndForm Composite : Being → Prop)
    (essenceOf esseOf : Being → Principle) : Prop :=
  (∀ x, ComposedOfMatterAndForm x → Composite x) ∧
    ∃ x, esseOf x ≠ essenceOf x ∧ ¬ Composite x

/-- Rival to `NoComponentIsFirstBeingReading`, motivated by the positions
Aquinas himself reports in q.3 a.8 (God as the soul of the world, God as the
formal principle of all things, God as prime matter) and by pantheist and
panentheist accounts on which the first principle is an ingredient of the
world: some first being is a component of something other than itself.

Ordinary meaning: what is first enters into the make-up of other things. The
standard example is a world-soul: nothing is prior to it, and it is the form of
the cosmos. It is not the claim that every first being is a component, and it
is not the claim that the first being is itself composite. The replacement
account is that being a constituent does not subordinate: the whole depends on
the first principle that informs it, not the other way round.

Strictly stronger than the negation of the premise: the negation allows a first
being that is a component only of itself, this requires a distinct whole. -/
def FirstBeingIsAComponentReading {Being : Sort u}
    (ComponentOf PriorSimply : Being → Being → Prop) : Prop :=
  ∃ p x, p ≠ x ∧ ComponentOf p x ∧ IsFirstBeing PriorSimply p

/-- Rival to `ImmaterialIsIntellectualReading`, motivated by physicalism about
the mind together with realism about immaterial things (abstract objects, or an
impersonal first principle such as Plotinus's One, which is beyond intellect):
whatever has intellect is composed of matter and form, and something is
altogether immaterial.

Ordinary meaning: thinking is what suitably organized material things do, and
immateriality does not make a thing a knower. The standard example is a number:
neither made of matter nor a component of anything, and it knows nothing. It is
not the denial that there are immaterial things (the second conjunct asserts
one), and it is not eliminativism about intellect. The replacement account of
why a thing knows is material organization, not separation from matter.

Strictly stronger than the negation of the premise: the negation needs one
altogether immaterial thing without intellect, this denies intellect to every
thing that is not composed of matter and form. -/
def IntellectOnlyInMaterialCompositesReading {Being : Sort u}
    (ComposedOfMatterAndForm HasIntellect : Being → Prop)
    (ComponentOf : Being → Being → Prop) : Prop :=
  (∀ x, HasIntellect x → ComposedOfMatterAndForm x) ∧
    ∃ x, ¬ ComposedOfMatterAndForm x ∧ ∀ y, ¬ ComponentOf x y

/-- Rival to `WillFollowsIntellectReading`, motivated by accounts of a purely
contemplative first intellect (Aristotle's thought thinking itself), by
Spinoza's denial that God acts from freedom of will, and by necessary
emanation: something has intellect and has no will.

Ordinary meaning: understanding does not bring with it wanting or choosing.
The standard example is a mind that only contemplates, from which things follow
by necessity and not by choice. It is not the claim that no intellect has will.
The replacement account of how anything proceeds from such an intellect is
necessity of nature, not volition.

This is the exact negation of the premise (an existential witness against a
universal); its positive content is in the motivating account, which this
carrier cannot express beyond the two predicates. -/
def IntellectWithoutWillReading {Being : Sort u} (HasIntellect HasWill : Being → Prop) :
    Prop :=
  ∃ x, HasIntellect x ∧ ¬ HasWill x

/-- Rival to `SubsistentBeingIsInfiniteReading`, motivated by the "thin" view
of existence (existence adds no perfection, so a thing's being its own existence
settles nothing about how much it is; Kenny's criticism of *ipsum esse
subsistens*) and by accounts of finite self-existent things: something is its
own act of being and is not infinite.

Ordinary meaning: existing of oneself is one thing, being unlimited another.
The proposed example is a necessarily existing abstract object or a finite
necessary being: its essence involves its existence, and it is limited to being
just what it is. It is not the claim that nothing is infinite, and it is not the
denial that some essence is identical with its act of being. The replacement
account is that limitation comes from what a thing is, not from its essence
receiving being.

This is the exact negation of the premise (an existential witness against a
universal); its positive content is in the motivating account, which this
carrier cannot express beyond the two principles and one predicate. -/
def FiniteSubsistentBeingReading {Being : Sort u} {Principle : Sort w}
    (essenceOf esseOf : Being → Principle) (Infinite : Being → Prop) : Prop :=
  ∃ x, esseOf x = essenceOf x ∧ ¬ Infinite x

/-- Rival to `ImmutableIsEternalReading`, motivated by the view that time passes
without change (Newton's absolute duration; Shoemaker's worlds with changeless
intervals) and by accounts of an everlasting God who is in time: something is in
potency in no respect and is not eternal.

Ordinary meaning: a thing that cannot change can still last through time. The
proposed example is an unchangeable being that exists at every moment, with a
before and an after in its duration though with no difference between them. It
is not the claim that such a thing begins or ends, and it is not the denial that
anything is immutable. The replacement account of its duration is everlasting
existence in time (sempiternity), which
`DISAMB-ETERNITY-AND-TEMPORAL-PERPETUITY` keeps apart from timeless eternity;
this carrier has only the predicate `Eternal`, so the rival's positive duration
claim is not expressed here, only the failure of `Eternal`.

This is the exact negation of the premise (an existential witness against a
universal). -/
def ImmutableWithoutEternityReading {Being : Sort u} {Respect : Sort v}
    (InPotency : Being → Respect → Prop) (Eternal : Being → Prop) : Prop :=
  ∃ x, PureAct InPotency x ∧ ¬ Eternal x

/-- Rival to `ClassicalAttributesSuffice`, motivated by the fuller list of
*Dei Filius* ch. 1 itself (*omnipotens*, *immensus*, *incomprehensibilis*) and
by accounts on which omnipotence, omniscience or omnipresence are not contained
in the nine: some being is simple, perfect, good, one, infinite, immutable,
eternal and has intellect and will, and does not have the classical attributes.

Ordinary meaning: the nine listed predicates are not the whole classical
profile. The proposed example is a being with all nine, as encoded, that is not
omnipotent. It is not the denial that the classical God has the nine, and it is
not a claim about which further attribute is missing. The replacement account
is that the classical profile has further members that the nine predicates, as
this corpus encodes them, do not entail.

This is the exact negation of the premise (an existential witness against a
universal), on the same `Signature` and the same nine predicates. -/
def ClassicalAttributesFallShort (σ : Signature)
    (Simple Perfect Good One Infinite Immutable Eternal HasIntellect HasWill :
      σ.Being → Prop) : Prop :=
  ∃ g, Simple g ∧ Perfect g ∧ Good g ∧ One g ∧ Infinite g ∧ Immutable g ∧ Eternal g ∧
    HasIntellect g ∧ HasWill g ∧ ¬ σ.HasClassicalAttributes g

/-! ## Finite tests

One namespace per premise. Each `Holds` lists: the rival, every other premise of
the named consuming theorem, and the failure of that theorem's conclusion. The
general logical premise `ExcludedMiddle` of two consumers is not a statement
about the interpretation and is not listed. -/

namespace Control

open TruthCore.Alternatives.ActPotencyRegress
open TruthCore.Alternatives.FideismReference
open TruthCore.Alternatives.NameApplicationTransfer
open TruthCore.Causality.CausalMapsBatch1
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryFirstBeing
open TruthCore.Causality.NecessaryFirstAttributes
open TruthCore.Causality.Round2ExistenceAct
open TruthCore.Causality.ExistenceActuality (ExistingInActAt)
open TruthCore.Causality.PureActThisness (FirstMoverHasEveryPureDetermination)
open TruthCore.Causality.WholePowerPerfection (InfiniteHasEveryPurePerfection)
open TruthCore.Greek.Aristotle.Metaphysics (CauseOfQualityInAnotherIsMoreSuchReading)
open TruthCore.German.Kant.CosmologicalInference (Ontic)

/-! Actuality without being (existing rival `ActualityWithoutBeingReading`)
against `Round2ExistenceAct.existingInActAtFromSomeAct`: one existent that is in
act in the non-esse respect only. -/
namespace actualityWithoutBeing
abbrev ontic : Ontic Unit Unit := ⟨⟨fun _ _ => True⟩, fun _ _ => True, fun _ _ _ => False⟩
abbrev esse : Bool := false
abbrev InAct : Unit → Bool → Prop := fun _ r => r = true
def Holds : Prop :=
  ActualityWithoutBeingReading InAct esse ∧
  ExistentInActInSomeRespectAt ontic InAct () ∧
  ¬ ExistingInActAt ontic InAct esse ()
end actualityWithoutBeing

/-! Emergent perfection against `CausalMapsBatch1.causeOfBeingHasWhatItGives`:
`false` causes `true` to be and to be alive (`r = true`); `false` has being
only. -/
namespace emergentPerfection
abbrev esse : Bool := false
abbrev CausesIn : Bool → Bool → Bool → Prop := fun c x _ => c = false ∧ x = true
abbrev InAct : Bool → Bool → Prop := fun x r => x = true ∨ r = false
def Holds : Prop :=
  EmergentPerfectionReading InAct CausesIn esse ∧
  CausedPerfectionIsHad CausesIn InAct ∧
  ¬ CauseOfBeingHasWhatItGives CausesIn InAct esse
end emergentPerfection

/-! Actuality without goodness against `StageTwo.GodIsSupremelyGood`: the one
being is God, maximal and in act, and good in nothing. -/
namespace actualityWithoutGoodness
abbrev IsGod : Unit → Prop := fun _ => True
abbrev InAct : Unit → Unit → Prop := fun _ _ => True
abbrev GoodIn : Unit → Unit → Prop := fun _ _ => False
abbrev MoreIn : Unit → Unit → Unit → Prop := fun _ _ _ => False
abbrev CausesIn : Unit → Unit → Unit → Prop := fun _ _ _ => False
def Holds : Prop :=
  ActualityNotSufficientForGoodnessReading GoodIn InAct ∧
  GodIsMaximalInBeing IsGod InAct MoreIn () ∧
  MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn ∧
  ActualityOnlyInsofarAsBeingReading InAct () ∧
  CauseOfBeingCausesEveryPerfection InAct CausesIn () ∧
  ¬ GodIsSupremelyGood IsGod InAct GoodIn CausesIn ()
end actualityWithoutGoodness

/-! Uncaused composite against `StageTwo.GodIsSimple`: the one being is God,
maximal, composite and caused by nothing. -/
namespace uncausedComposite
abbrev IsGod : Unit → Prop := fun _ => True
abbrev Composite : Unit → Prop := fun _ => True
abbrev InAct : Unit → Unit → Prop := fun _ _ => True
abbrev MoreIn : Unit → Unit → Unit → Prop := fun _ _ _ => False
abbrev CausesIn : Unit → Unit → Unit → Prop := fun _ _ _ => False
def Holds : Prop :=
  UncausedCompositeReading Composite CausesIn () ∧
  GodIsMaximalInBeing IsGod InAct MoreIn () ∧
  CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn ∧
  ¬ GodIsSimple IsGod Composite
end uncausedComposite

/-! Esse-essence difference without composition against
`FirstMoverSimple.firstMoverSimple`: `true` moves `false` and is moved by
nothing; nothing is a body, a matter-form composite, composite or a component;
every being's act of being (`true`) differs from its essence (`false`). -/
namespace differenceWithoutComposition
abbrev MovedIn : Bool → Unit → Prop := fun x _ => x = false
abbrev MovesIn : Bool → Bool → Unit → Prop := fun y x _ => y = true ∧ x = false
abbrev PriorSimply : Bool → Bool → Prop := fun y x => y = true ∧ x = false
abbrev ComponentOf : Bool → Bool → Prop := fun _ _ => False
abbrev Never : Bool → Prop := fun _ => False
abbrev essenceOf : Bool → Bool := fun _ => false
abbrev esseOf : Bool → Bool := fun _ => true
def Holds : Prop :=
  EsseEssenceDifferenceWithoutCompositionReading Never Never essenceOf esseOf ∧
  NoBodyMovesUnlessMovedReading MovedIn MovesIn Never ∧
  FirstUnmovedMoverIsFirstBeing MovedIn MovesIn PriorSimply ∧
  CompositePosteriorToComponentsReading ComponentOf PriorSimply ∧
  CompositeHasComponentOtherThanItselfReading Never ComponentOf ∧
  ¬ FirstUnmovedMoverIsSimpleReading MovedIn MovesIn Never Never Never essenceOf esseOf
end differenceWithoutComposition

/-! A first being that is a component against
`NecessaryFirstAttributes.attributesFromFirst`: one world; `true` (the informing
principle) and `false` (the whole) both exist, are concrete and ungrounded;
`true` is simply prior to `false` and is its component; nothing is in potency;
`false` is composite. -/
namespace firstBeingComponent
abbrev profile : Profile Unit Bool :=
  ⟨⟨⟨fun _ _ => True⟩, fun _ _ => True, fun _ _ _ => False⟩, fun _ => True,
    fun _ _ _ => False⟩
abbrev PriorSimply : Bool → Bool → Prop := fun y x => y = true ∧ x = false
abbrev ComponentOf : Bool → Bool → Prop := fun p x => p = true ∧ x = false
abbrev InPotency : Bool → Unit → Prop := fun _ _ => False
abbrev Composite : Bool → Prop := fun x => x = false
def Holds : Prop :=
  FirstBeingIsAComponentReading ComponentOf PriorSimply ∧
  NecessaryActualFirstPureActAt profile () PriorSimply InPotency ∧
  CompositePosteriorToComponentsReading ComponentOf PriorSimply ∧
  CompositeHasComponentOtherThanItselfReading Composite ComponentOf ∧
  ¬ NecessaryFirstAttributesAt profile () PriorSimply ComponentOf InPotency Composite
end firstBeingComponent

/-! Intellect only in material composites against `StageTwo.GodHasIntellect`:
`true` is God, immaterial, maximal, first and without intellect; `false` is a
matter-form composite with intellect, caused to be by `true`, with an act of
being other than its essence. -/
namespace materialIntellect
abbrev IsGod : Bool → Prop := fun x => x = true
abbrev Material : Bool → Prop := fun x => x = false
abbrev Composite : Bool → Prop := fun x => x = false
abbrev HasIntellect : Bool → Prop := fun x => x = false
abbrev ComponentOf : Bool → Bool → Prop := fun _ _ => False
abbrev PriorSimply : Bool → Bool → Prop := fun _ _ => False
abbrev essenceOf : Bool → Bool := fun _ => true
abbrev esseOf : Bool → Bool := fun x => x
abbrev InAct : Bool → Unit → Prop := fun _ _ => True
abbrev MoreIn : Unit → Bool → Bool → Prop := fun _ y x => y = true ∧ x = false
abbrev CausesIn : Bool → Bool → Unit → Prop := fun c x _ => c = true ∧ x = false
def Holds : Prop :=
  IntellectOnlyInMaterialCompositesReading Material HasIntellect ComponentOf ∧
  (∃ x, HasIntellect x) ∧
  GodIsMaximalInBeing IsGod InAct MoreIn () ∧
  CompositeHasAUnitingCauseReading Composite CausesIn () ∧
  CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn ∧
  MatterFormAndEsseEssenceAreCompositionsReading Material Composite essenceOf esseOf ∧
  NoComponentIsFirstBeingReading ComponentOf PriorSimply ∧
  MaximumInBeingIsFirstBeing InAct MoreIn () PriorSimply ∧
  ¬ GodHasIntellect IsGod HasIntellect
end materialIntellect

/-! Intellect without will against `StageTwo.GodHasWill`: the one being is God,
immaterial, simple, maximal and first, has intellect and has no will. -/
namespace intellectWithoutWill
abbrev Always : Unit → Prop := fun _ => True
abbrev Never : Unit → Prop := fun _ => False
abbrev NoRel : Unit → Unit → Prop := fun _ _ => False
abbrev principle : Unit → Unit := fun _ => ()
abbrev InAct : Unit → Unit → Prop := fun _ _ => True
abbrev MoreIn : Unit → Unit → Unit → Prop := fun _ _ _ => False
abbrev CausesIn : Unit → Unit → Unit → Prop := fun _ _ _ => False
def Holds : Prop :=
  IntellectWithoutWillReading Always Never ∧
  GodIsMaximalInBeing Always InAct MoreIn () ∧
  CompositeHasAUnitingCauseReading Never CausesIn () ∧
  CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn ∧
  MatterFormAndEsseEssenceAreCompositionsReading Never Never principle principle ∧
  NoComponentIsFirstBeingReading NoRel NoRel ∧
  MaximumInBeingIsFirstBeing InAct MoreIn () NoRel ∧
  ImmaterialIsIntellectualReading Never Always NoRel ∧
  ¬ GodHasWill Always Never
end intellectWithoutWill

/-! Potency prior to act (existing rival `PotencyPriorToActReading`) against
`FirstBeingNoPotency.firstBeingNoPotency`: the one being is in potency, nothing
is in act, nothing is prior to anything. -/
namespace potencyPrior
abbrev InPotency : Unit → Unit → Prop := fun _ _ => True
abbrev InAct : Unit → Unit → Prop := fun _ _ => False
abbrev PriorSimply : Unit → Unit → Prop := fun _ _ => False
def Holds : Prop :=
  PotencyPriorToActReading InAct InPotency PriorSimply ∧
  NotActAndPotencyInSameRespectReading InAct InPotency ∧
  ¬ FirstBeingIsInNoWayInPotencyReading InPotency PriorSimply
end potencyPrior

/-! Act and potency in the same respect (existing rival
`InActAndPotencyInSameRespectReading`) against
`FirstBeingNoPotency.firstBeingNoPotency`: the one being is in act and in
potency in the one respect and is simply prior to itself. -/
namespace actAndPotency
abbrev InPotency : Unit → Unit → Prop := fun _ _ => True
abbrev InAct : Unit → Unit → Prop := fun _ _ => True
abbrev PriorSimply : Unit → Unit → Prop := fun _ _ => True
def Holds : Prop :=
  InActAndPotencyInSameRespectReading InAct InPotency ∧
  ActSimplyPriorToPotencyReading InAct InPotency PriorSimply ∧
  ¬ FirstBeingIsInNoWayInPotencyReading InPotency PriorSimply
end actAndPotency

/-! Finite subsistent being against
`WholePowerPerfection.firstMoverPerfectionFromInfinity`: the one being moves
itself in the sense of `MovesIn` without being moved, is simple, is its own act
of being, is not infinite and lacks the one pure perfection. -/
namespace finiteSubsistent
abbrev Moved : Unit → Unit → Prop := fun _ _ => False
abbrev Moves : Unit → Unit → Unit → Prop := fun _ _ _ => True
abbrev Never : Unit → Prop := fun _ => False
abbrev Always : Unit → Prop := fun _ => True
abbrev principle : Unit → Unit := fun _ => ()
abbrev Has : Unit → Unit → Prop := fun _ _ => False
def Holds : Prop :=
  FiniteSubsistentBeingReading principle principle Never ∧
  FirstUnmovedMoverIsSimpleReading Moved Moves Never Never Never principle principle ∧
  InfiniteHasEveryPurePerfection Never Has Always ∧
  ¬ FirstMoverHasEveryPureDetermination Moved Moves Has Always
end finiteSubsistent

/-! Immutable without eternity against `StageTwo.GodIsEternal`: the one being
is God, maximal, first, in act, in potency in no respect, and not eternal. -/
namespace immutableInTime
abbrev Always : Unit → Prop := fun _ => True
abbrev Never : Unit → Prop := fun _ => False
abbrev InPotency : Unit → Unit → Prop := fun _ _ => False
abbrev InAct : Unit → Unit → Prop := fun _ _ => True
abbrev MoreIn : Unit → Unit → Unit → Prop := fun _ _ _ => False
abbrev PriorSimply : Unit → Unit → Prop := fun _ _ => False
def Holds : Prop :=
  ImmutableWithoutEternityReading InPotency Never ∧
  GodIsMaximalInBeing Always InAct MoreIn () ∧
  MaximumInBeingIsFirstBeing InAct MoreIn () PriorSimply ∧
  ActSimplyPriorToPotencyReading InAct InPotency PriorSimply ∧
  NotActAndPotencyInSameRespectReading InAct InPotency ∧
  ¬ GodIsEternal Always Never
end immutableInTime

/-! Failure of the full naming leaf (existing rival `FullNominalNamingFails`)
with its motivating practice-use thesis, against
`NameApplicationTransfer.Description.properDescriptionExcluded`: the one being
meets the full description; the practice's name refers to nothing; nothing is
God in the proper sense. -/
namespace namingFails
abbrev practice : NamingPractice Unit :=
  { Move := Unit, Correct := fun _ => True, OwnStandard := fun _ => True,
    Defined := fun _ => True, AffirmsNaturalKnowability := fun _ => False,
    AnswersToSharedReason := fun _ => False, Name := Unit,
    RefersTo := fun _ _ => False, ConfessesReferent := fun _ _ => False }
abbrev proper : Unit → Prop := fun _ => False
abbrev InAct : Unit → Unit → Prop := fun _ _ => True
abbrev MoreIn : Unit → Unit → Unit → Prop := fun _ _ _ => False
abbrev CausesIn : Unit → Unit → Unit → Prop := fun _ _ _ => False
abbrev ComponentOf : Unit → Unit → Prop := fun _ _ => False
def Holds : Prop :=
  FullNominalNamingFails InAct MoreIn CausesIn () ComponentOf proper ∧
  GodNamesNoBeingReading practice () ∧
  ProperReferencePreserved practice () proper ∧
  FullDescriptorExists InAct MoreIn CausesIn () ComponentOf ∧
  ¬ FullDescriptionExcluded InAct MoreIn CausesIn () ComponentOf
end namingFails

/-! The nine attributes falling short against
`StageTwo.ClassicalAttributes.godHasClassicalAttributes`: the one being is God
and has all nine predicates; the primitive classical-attributes field is false
of it. -/
namespace attributesFallShort
abbrev sig : Signature :=
  { Being := Unit, IsGod := fun _ => True, HasClassicalAttributes := fun _ => False,
    RevealsRecognizably := fun _ => False, jesus := (),
    ClaimedDivineAuthority := fun _ => False, RoseFromTheDead := fun _ => False,
    Society := Unit, catholicChurch := (), Founded := fun _ _ => False,
    VisibleWithAuthority := fun _ => False,
    FoundedAsTeachingAuthority := fun _ _ => False,
    DefinitivelyProposesAsRevealed := fun _ _ => False,
    creedOneGodFatherAlmightyCreator := False,
    creedOneLordJesusChristOnlyBegottenConsubstantial := False,
    creedIncarnateOfSpiritAndVirginMary := False,
    creedCrucifiedUnderPilateSufferedBuried := False,
    creedRoseOnTheThirdDay := False,
    creedAscendedSeatedAtRightHand := False,
    creedWillComeToJudgeKingdomWithoutEnd := False,
    creedHolySpiritLordGiverOfLife := False,
    creedOneHolyCatholicApostolicChurch := False,
    creedOneBaptismForForgiveness := False,
    creedResurrectionOfTheDead := False,
    creedLifeOfTheWorldToCome := False }
abbrev Always : Unit → Prop := fun _ => True
abbrev Never : Unit → Prop := fun _ => False
abbrev InAct : Unit → Unit → Prop := fun _ _ => True
abbrev GoodIn : Unit → Unit → Prop := fun _ _ => True
abbrev MoreIn : Unit → Unit → Unit → Prop := fun _ _ _ => False
abbrev CausesIn : Unit → Unit → Unit → Prop := fun _ _ _ => False
def Holds : Prop :=
  ClassicalAttributesFallShort sig (IsSimple Never) (IsPerfect InAct)
    (IsSupremelyGood InAct GoodIn CausesIn ()) (IsTheOneGod sig.IsGod)
    Always Always Always Always Always ∧
  GodIsMaximalInBeing sig.IsGod InAct MoreIn () ∧
  MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn ∧
  CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn ∧
  CompositeHasAUnitingCauseReading Never CausesIn () ∧
  ActualityOnlyInsofarAsBeingReading InAct () ∧
  PerfectionsOfEffectPreexistInCauseReading InAct CausesIn () ∧
  GoodnessIsActualityReading GoodIn InAct ∧
  CauseOfBeingCausesEveryPerfection InAct CausesIn () ∧
  GodIsInfinite sig.IsGod Always ∧
  GodIsImmutable sig.IsGod Always ∧
  GodIsEternal sig.IsGod Always ∧
  GodHasIntellect sig.IsGod Always ∧
  GodHasWill sig.IsGod Always ∧
  ¬ GodHasClassicalAttributes sig
end attributesFallShort

/-- The fourteen finite tests, one per stage-two attribute premise. -/
def Certificate : Prop :=
  actualityWithoutBeing.Holds ∧ emergentPerfection.Holds ∧
  actualityWithoutGoodness.Holds ∧ uncausedComposite.Holds ∧
  differenceWithoutComposition.Holds ∧ firstBeingComponent.Holds ∧
  materialIntellect.Holds ∧ intellectWithoutWill.Holds ∧
  potencyPrior.Holds ∧ actAndPotency.Holds ∧ finiteSubsistent.Holds ∧
  immutableInTime.Holds ∧ namingFails.Holds ∧ attributesFallShort.Holds

end Control

end TruthCore.Causality.SpineRivalsAttributes
