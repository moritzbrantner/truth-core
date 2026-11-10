module

public import TruthCore.Causality.NecessaryConcreteUnderived
public import TruthCore.Causality.WholeRosterFoundation
public import TruthCore.Causality.NecessaryFirstBeing
public import TruthCore.Causality.DirectEsseRootUniquenessAtBeing
public import TruthCore.Causality.SelectedAncestry
public import TruthCore.Causality.ActualRootUniqueness
public import TruthCore.Causality.Round2Grounding
public import TruthCore.Causality.Round2ExistenceAct
public import TruthCore.Causality.TermSenseForks3
public import TruthCore.Case.Catholicism.CausalPerfectionTransfer
public import TruthCore.Case.Catholicism.StageTwo
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article7Cause

/-!
# Rivals of twelve spine premises: regress and root, act of being, and the join

Analyst formulations, attribution deferred. Nothing here is attributed to an
author; "motivated by" names the ordinary position a rival is meant to capture.

Target: twelve open premises on verified routes to `STMT-GOD-EXISTS` (stage two
of the modal spine: `NecessaryClassicalGodRoot.derive` and the join
`NecessaryConcreteUnderived`). For each premise this module states one rival on
the **same carrier and vocabulary** as the premise. A rival is a positive
position: it says what its holder asserts instead, and it is incompatible with
the premise on that carrier (helpers `…_excludes` in the Solution module). The
rival of `EveryContingentGroundedAt` is the existing
`NecessaryRootFork.ContingentRootAt`; the other eleven are defined here.

`Control` holds one explicit interpretation per premise: the rival holds
together with every other premise of the premise's smallest consuming theorem,
and that theorem's conclusion fails. Each certificate is a statement about one
interpretation. It is no evidence that the rival is true or metaphysically
possible, and it does not refute or establish the premise. No premise of any
route is derived, added or removed.
-/

@[expose] public section

namespace TruthCore.Causality.SpineRivalsRootEsse

open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryRootFork
open TruthCore.Causality.CogitoNecessaryConcrete (ActualConcreteGround)
open TruthCore.German.Kant.CosmologicalInference (Ontic NecessaryAt ContingentAt)
open TruthCore.Latin.Aquinas.SummaTheologiae

variable {W B R : Type}

/-! ## Regress and root premises -/

/-- Rival of `InhabitedConcreteAt` (motivated by abstract-only ontologies:
Pythagorean or mathematical-structure monism, on which what there is at bottom
is structure and nothing is a concrete thing). Something exists at `w`, and
nothing that exists at `w` is concrete.

Example: a world whose whole inventory is numbers and structures. It is not the
empty world (something exists) and not a claim that concreta are impossible.
Stronger than the negation of the premise: it adds population. -/
def OnlyNonConcreteExistAt (m : Ontic W B) (concrete : B → Prop) (w : W) : Prop :=
  (∃ b, m.ExistsAt w b) ∧ ∀ b, m.ExistsAt w b → ¬ concrete b

/-- Rival of `WholeRosterNotTrapped` (motivated by metaphysical infinitism and
coherentism about dependence: reality has no fundamental level). The actual
concrete roster at `w` is inhabited, and every actual concretum has an actual
concrete ground under the selected relation at `w`.

Example: an endless descending series in which each thing is grounded by the
next, or a closed circle of mutual grounding. It does not say which of the two
shapes obtains, and it says nothing about non-concrete or absent grounds.
It implies the negation of the premise (`bottomless_excludes`); the converse
is not checked here. -/
def BottomlessActualGroundingAt (m : Profile W B) (w : W) : Prop :=
  (∃ x, ActualConcrete m w x) ∧
    ∀ x, ActualConcrete m w x → ∃ y, ActualConcreteGround m w y x

/-! ## Act-of-being bridges -/

/-- Rival of `MaximumInBeingCausesAllBeingsReading` (motivated by eminence
without universal efficient causation: a highest being that is an exemplar or
final cause only, as with Aristotle's unmoved mover or Epicurean gods, while a
lesser agent makes things be). Some maximum in being does not cause the being of
some other being, whose being is caused by a third thing distinct from both.

Example: a supreme exemplar, a craftsman below it, and an artefact whose being
the craftsman causes. It is not the claim that there is no maximum, and not the
claim that the maximum causes nothing. Stronger than the negation: it names
the replacing cause. -/
def SomeMaximumLeavesBeingToAnother (InAct : B → R → Prop)
    (MoreIn : R → B → B → Prop) (CausesIn : B → B → R → Prop) (esse : R) : Prop :=
  ∃ m x c, IsMaximumIn InAct MoreIn esse m ∧ x ≠ m ∧ InAct x esse ∧
    ¬ CausesIn m x esse ∧ c ≠ m ∧ c ≠ x ∧ CausesIn c x esse

/-- Rival of `ExistingInActAt` (motivated by the thin, quantificational
conception of existence: to exist is to be something, and existence is not an
actuality a thing has in some respect). Something exists at `w`, and nothing
that exists at `w` is in act in the supplied esse respect.

Example: on this view "Socrates exists" says that something is Socrates, and
ascribes no act of being to him. It does not deny that things exist, and it
says nothing about act in respects other than esse. Stronger than the
negation: no existent at `w`, not merely some, has the act. -/
def ExistenceWithoutActOfBeingAt (m : Ontic W B) (InAct : B → R → Prop)
    (esse : R) (w : W) : Prop :=
  (∃ x, m.ExistsAt w x) ∧ ∀ x, m.ExistsAt w x → ¬ InAct x esse

/-- Rival of `EsseCauseIsActualConcreteGround` (motivated by non-concrete
causes of being: Platonic Forms, or governing laws of nature, as what makes a
concrete thing be). Some actual concretum has a distinct cause of its esse that
exists at `w` and is not concrete.

Example: the Form of the Good causing the being of a concrete thing. It is not
the claim that the cause is absent, and it leaves open whether the selected
relation holds between the two. Stronger than the negation: it fixes which
clause of the bridge fails (concreteness of the cause). -/
def SomeEsseCauseNonConcrete (m : Profile W B) (w : W)
    (CausesIn : B → B → R → Prop) (esse : R) : Prop :=
  ∃ c x, c ≠ x ∧ ActualConcrete m w x ∧ CausesIn c x esse ∧
    m.ontic.ExistsAt w c ∧ ¬ m.concrete c

/-- Rival of `GradesToMaximumAtBeing` (motivated by open-ended hierarchy: more
and less need no most, as the natural numbers have greater and smaller but no
greatest). Some pair compares in esse, and every individual in act in esse is
exceeded in esse by another individual in act in esse.

Example: an endless ascending scale of beings. It is not the claim that
nothing compares, and it imposes no order laws on `MoreIn`. Stronger than the
negation: the exceeding individual is itself in act. The existing
`QuartaViaUnboundedDegrees` is not reused: it holds on an empty carrier, where
the premise also holds, so the two are not incompatible. -/
def EveryActualGradeExceededAtBeing (InAct : B → R → Prop)
    (MoreIn : R → B → B → Prop) (esse : R) : Prop :=
  (∃ x y, MoreIn esse x y) ∧
    ∀ n, InAct n esse → ∃ y, InAct y esse ∧ MoreIn esse y n

/-- Rival of `UniversalCauseTransfersPerfections` (motivated by mere
conservationism: the first cause gives and conserves being, and creatures
alone produce their further perfections). Some cause of the being of every
other being causes the esse of a distinct effect, yet does not cause one of
that effect's actual perfections, which a cause other than it does cause.

Example: a universal source keeps a pupil in being while a teacher alone
causes the pupil's skill. It is not occasionalism (the secondary cause really
causes) and not concurrentism (the universal cause does not co-cause the
perfection). Stronger than the negation: it names the secondary cause. -/
def UniversalCauseLeavesPerfectionToSecondary (InAct : B → R → Prop)
    (CausesIn : B → B → R → Prop) (esse : R) : Prop :=
  ∃ c x r d, CausesAllInGenus InAct CausesIn esse c ∧ x ≠ c ∧ CausesIn c x esse ∧
    InAct x r ∧ ¬ CausesIn c x r ∧ d ≠ c ∧ CausesIn d x r

/-- Rival of `SimplyPriorIsActualConcreteGround` (motivated by Platonism about
priority: Forms, numbers or laws are simply prior to concrete things without
being concrete). Something not concrete is simply prior to a distinct actual
concretum.

Example: the number two, or the Form of the Good, prior to a concrete thing.
It is not the claim that the prior thing is absent or that priority is temporal.
Stronger than the negation: it fixes which clause fails (concreteness). -/
def SomeSimplyPriorNonConcrete (m : Profile W B) (w : W)
    (PriorSimply : B → B → Prop) : Prop :=
  ∃ y x, y ≠ x ∧ PriorSimply y x ∧ ActualConcrete m w x ∧ ¬ m.concrete y

/-- Rival of `GodIsMaximalInBeing` (motivated by demiurgic and finite-god
theologies: the Demiurge of the *Timaeus* below the Good, or a limited God).
Something is God, has being, and is exceeded in being by something that is not
God.

Example: a divine craftsman who looks to a Form more real than himself. It is
not atheism (something is God) and not the claim that God lacks being.
Stronger than the negation: the god has being and what exceeds it is not God. -/
def SomeGodExceededInBeing (IsGod : B → Prop) (InAct : B → R → Prop)
    (MoreIn : R → B → B → Prop) (esse : R) : Prop :=
  ∃ g y, IsGod g ∧ InAct g esse ∧ ¬ IsGod y ∧ MoreIn esse y g

/-! ## Join premises -/

/-- Rival of `NoContingentConcreteSupport` (motivated by bottom-up grounding of
a necessary whole: a necessarily existing cosmos or spacetime sustained, where
it is sustained, by constituents that might not have existed). At some admitted
world, a concrete candidate existing there supports a concrete candidate that
is necessary from `w`, and the supporter is absent from some world accessible
from `w`.

Example: a necessary whole whose parts differ from world to world. It does
not say the necessary thing is supported at `w` itself or at every world.
It implies the negation of the premise constructively; with excluded middle it
is equivalent to it (the absent-at world is exhibited, not merely denied). -/
def SomeNecessaryConcretumContingentlySupported (m : Profile W B) (w : W) : Prop :=
  ∃ v a b, m.concrete a ∧ m.concrete b ∧ m.ontic.ExistsAt v a ∧
    NecessaryAt m.ontic w b ∧ m.grounds v a b ∧
    ∃ u, m.ontic.frame.access w u ∧ ¬ m.ontic.ExistsAt u a

/-- Rival of `ConcreteNecessaryUnionWF` (motivated by metaphysical
interdependence: necessary beings that support each other, with the direction
of support differing between worlds). Two concrete candidates necessary from
`w` are such that the first, existing at one admitted world, supports the second
there, and the second, existing at an admitted world, supports the first there.

Example: two necessary beings, each of which sustains the other in a different
possible world. The two candidates may coincide (a self-supporter) and the two
worlds may coincide (a circle within one world). It is not a regress without
end. Stronger than the negation: non-well-foundedness could also come from an
endless descending chain. -/
def NecessaryConcretaMutualSupport (m : Profile W B) (w : W) : Prop :=
  ∃ a b v u, m.concrete a ∧ m.concrete b ∧ NecessaryAt m.ontic w a ∧
    NecessaryAt m.ontic w b ∧ m.ontic.ExistsAt v a ∧ m.grounds v a b ∧
    m.ontic.ExistsAt u b ∧ m.grounds u b a

/-! ## Interpretations

One explicit interpretation per premise. Each is a formal structure only. -/

namespace Control

open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)
open TruthCore.Logic.CogitoEsse (IntellectualExerciseRequiresAct)
open TruthCore.Causality.Round2ExistenceAct (IntellectualExerciserExistsAt)
open TruthCore.Causality.Round2Grounding (ContingentConcretumParticipatesEsse
  ParticipatedEsseHasDistinctCause)
open TruthCore.Causality.ExistenceActuality (ExistingInActAt)
open TruthCore.Causality.NecessaryConcreteRouteBridge (EsseCauseIsActualConcreteGround
  SimplyPriorIsActualConcreteGround)
open TruthCore.Causality.WholeRosterFoundation (WholeRosterNotTrapped)
open TruthCore.Causality.NecessaryFirstBeing (NecessaryActualFirstAt)
open TruthCore.Causality.SelectedAncestry (NecessaryRootAncestor)
open TruthCore.Causality.ActualRootUniqueness (UniqueActualRootAt)
open TruthCore.Causality.NecessaryRootUniqueness (UniqueNecessaryActualRootAt)
open TruthCore.Causality.DirectEsseRootUniquenessAtBeing (GradesToMaximumAtBeing)
open TruthCore.Causality.TermSenseForks (SomeBeingMaximalInBeing)
open TruthCore.Causality.NecessarilyUnderived (ActualReflexive)
open TruthCore.Causality.NecessaryConcreteUnderived
open TruthCore.Case.Catholicism
open TruthCore.Greek.Aristotle.Metaphysics (CauseOfQualityInAnotherIsMoreSuchReading)
open TruthCore.Latin.Aquinas.SummaTheologiae.HumanIntellect (OperationAttribution)

/-- One world, one existing candidate, nothing concrete. -/
def abstractOnly : Profile Unit Unit where
  ontic := { frame := ⟨fun _ _ => True⟩, ExistsAt := fun _ _ => True, Causes := fun _ _ _ => False }
  -- category-constant: intended (the abstract-only rival: its point is that no candidate is concrete)
  concrete := fun _ => False
  grounds := fun _ _ _ => False

/-- The abstract-only rival holds with excluded middle, and the trilemma
concluded by `NecessaryRootFork.necessaryRootTrilemma` fails. -/
def AbstractOnlySurvives : Prop :=
  OnlyNonConcreteExistAt abstractOnly.ontic abstractOnly.concrete () ∧ ExcludedMiddle ∧
    ¬ NecessaryRootTrilemma abstractOnly ()

/-- Two mutually accessible worlds; the natural numbers exist at the selected
world `false` only; each number is grounded by its successor. -/
def descent : Profile Bool Nat where
  ontic := { frame := ⟨fun _ _ => True⟩, ExistsAt := fun w _ => w = false, Causes := fun _ _ _ => False }
  concrete := fun _ => True  -- category-constant: intended (all-concrete inventory: the model tests grounding structure, not the concrete/abstract line)
  grounds := fun _ a b => a = b + 1

/-- Bottomless grounding holds with the other premises of
`WholeRosterFoundation.necessaryConcrete`, and no concretum is necessary. -/
def BottomlessSurvives : Prop :=
  BottomlessActualGroundingAt descent false ∧
    InhabitedConcreteAt descent.ontic descent.concrete false ∧
    EveryContingentGroundedAt descent false ∧ ExcludedMiddle ∧
    ¬ NecessaryConcreteAt descent false

/-- Two mutually accessible worlds; one candidate, existing at the selected
world `false` only, with no ground. -/
def bruteRoot : Profile Bool Unit where
  ontic := { frame := ⟨fun _ _ => True⟩, ExistsAt := fun w _ => w = false, Causes := fun _ _ _ => False }
  concrete := fun _ => True  -- category-constant: intended (all-concrete inventory: the model tests grounding/modal structure, not the concrete/abstract line)
  grounds := fun _ _ _ => False

/-- A contingent root holds with the other premises of
`ActualRootNecessityUpgrade.upgrade`, and no unique necessary root exists. -/
def ContingentRootSurvives : Prop :=
  ContingentRootAt bruteRoot false ∧ UniqueActualRootAt bruteRoot false ∧ ExcludedMiddle ∧
    ¬ UniqueNecessaryActualRootAt bruteRoot false

/-- Three roles shared by two interpretations: a highest item, a middle agent
and a lowest recipient. -/
inductive Tier where
  | top | maker | made
  deriving DecidableEq

def tierAct (_ : Tier) (_ : Unit) : Prop := True
/-- The strict ranking top above maker above made, stated without a rank function. -/
def tierMore (_ : Unit) (y x : Tier) : Prop :=
  (y = .top ∧ x ≠ .top) ∨ (y = .maker ∧ x = .made)
/-- Only the middle agent causes being, and only in the lowest. -/
def tierCause (c x : Tier) (_ : Unit) : Prop := c = .maker ∧ x = .made

/-- The idle-maximum rival holds with the other premise of
`TermSenseForks3.maximeEnsCausesAllMaximal`, and no maximum in being causes the
being of every other being. -/
def IdleMaximumSurvives : Prop :=
  SomeMaximumLeavesBeingToAnother tierAct tierMore tierCause () ∧
    SomeBeingMaximalInBeing tierAct tierMore () ∧
    ¬ MaximeEnsCausesBeingOfAllReading tierAct tierMore tierCause ()

/-- One world, one existing candidate, no act in any respect. -/
def thinOntic : Ontic Unit Unit :=
  { frame := ⟨fun _ _ => True⟩, ExistsAt := fun _ _ => True, Causes := fun _ _ _ => False }
def thinAct (_ : Unit) (_ : Unit) : Prop := False
/-- The one candidate exercises intellect in the one episode. -/
def thinAttribution : OperationAttribution Unit Unit where
  IntellectualExercise := fun _ _ => True
  BodyShares := fun _ => False
  InheresAsAccidentOrMaterialForm := fun _ => False
  CompleteInSpecies := fun _ => False

/-- The thin-existence rival holds with the other premise of
`Round2ExistenceAct.intellectualExerciseRequiresActFromExistence`, and an
intellectual exerciser is in act in no respect. -/
def ThinExistenceSurvives : Prop :=
  ExistenceWithoutActOfBeingAt thinOntic thinAct () () ∧
    IntellectualExerciserExistsAt thinOntic thinAttribution () ∧
    ¬ IntellectualExerciseRequiresAct thinAttribution thinAct

/-- Two mutually accessible worlds. `false` is a non-concrete item existing at
both; `true` is a concrete item existing at the selected world `false` only.
The selected relation is empty. -/
def formCause : Profile Bool Bool where
  ontic := { frame := ⟨fun _ _ => True⟩, ExistsAt := fun w b => b = false ∨ w = false,
             Causes := fun _ _ _ => False }
  concrete := fun b => b = true
  grounds := fun _ _ _ => False

/-- The non-concrete item causes the esse of the concrete one. -/
def formCauses (c x : Bool) (_ : Unit) : Prop := c = false ∧ x = true
def formParticipates (x : Bool) : Prop := x = true

/-- A non-concrete esse cause holds with the other premises of
`Round2Grounding.contingentGroundedViaParticipation`, and an actual contingent
concretum has no actual concrete ground. -/
def NonConcreteEsseCauseSurvives : Prop :=
  SomeEsseCauseNonConcrete formCause false formCauses () ∧
    ContingentConcretumParticipatesEsse formCause false formParticipates ∧
    ParticipatedEsseHasDistinctCause formParticipates formCauses () ∧
    ¬ EveryContingentGroundedAt formCause false

/-- One world; the natural numbers all exist, are concrete and ungrounded. -/
def ascent : Profile Unit Nat where
  ontic := { frame := ⟨fun _ _ => True⟩, ExistsAt := fun _ _ => True, Causes := fun _ _ _ => False }
  concrete := fun _ => True  -- category-constant: intended (all-concrete inventory: the model tests the grades order, not the concrete/abstract line)
  grounds := fun _ _ _ => False

def ascentAct (_ : Nat) (_ : Unit) : Prop := True
/-- The greater number is more in esse. -/
def ascentMore (_ : Unit) (y x : Nat) : Prop := x < y
def ascentCause (_ _ : Nat) (_ : Unit) : Prop := False

/-- Unbounded grades hold with the other premises of
`SelectedAncestryUnique.uniqueRoot`, and no unique necessary root exists. -/
def UnboundedGradesSurvive : Prop :=
  EveryActualGradeExceededAtBeing ascentAct ascentMore () ∧
    NecessaryRootAncestor ascent () 0 ∧ ExcludedMiddle ∧
    MaximumInBeingCausesAllBeingsReading ascentAct ascentMore ascentCause () ∧
    ExistingInActAt ascent.ontic ascentAct () () ∧
    EsseCauseIsActualConcreteGround ascent () ascentCause () ∧
    ¬ UniqueNecessaryActualRootAt ascent ()

def conserveAct (_ : Tier) (_ : Bool) : Prop := True
/-- Respect `false` is esse, `true` a further perfection. The top causes the
esse of the other two; only the middle agent causes the further perfection, and
only in the lowest. -/
def conserveCause (c x : Tier) (r : Bool) : Prop :=
  (r = false ∧ c = .top ∧ x ≠ .top) ∨ (r = true ∧ c = .maker ∧ x = .made)

/-- Mere conservation holds with the other premise of
`CausalPerfectionTransfer.reconstruction`, and a cause of being fails to cause a
perfection of its effect. -/
def MereConservationSurvives : Prop :=
  UniversalCauseLeavesPerfectionToSecondary conserveAct conserveCause false ∧
    ResidualPerfectionTransfer conserveAct conserveCause false ∧
    ¬ CauseOfBeingCausesEveryPerfection conserveAct conserveCause false

/-- One world, two existing candidates: `true` concrete, `false` not. The
selected relation is empty. -/
def abstractPrior : Profile Unit Bool where
  ontic := { frame := ⟨fun _ _ => True⟩, ExistsAt := fun _ _ => True, Causes := fun _ _ _ => False }
  concrete := fun b => b = true
  grounds := fun _ _ _ => False

/-- The non-concrete item is simply prior to the concrete one. -/
def abstractPriorTo (y x : Bool) : Prop := y = false ∧ x = true

/-- A non-concrete simply prior item holds with the other premises of
`NecessaryFirstBeing.necessaryFirst`, and no necessary actual root is a first
being. -/
def AbstractPriorSurvives : Prop :=
  SomeSimplyPriorNonConcrete abstractPrior () abstractPriorTo ∧
    InhabitedConcreteAt abstractPrior.ontic abstractPrior.concrete () ∧
    WholeRosterNotTrapped abstractPrior () ∧
    EveryContingentGroundedAt abstractPrior () ∧ ExcludedMiddle ∧
    ¬ NecessaryActualFirstAt abstractPrior () abstractPriorTo

/-- `true` is a composite god; `false` exceeds it in being and causes its esse. -/
def demiurgeGod (b : Bool) : Prop := b = true
def demiurgeAct (_ : Bool) (_ : Unit) : Prop := True
def demiurgeMore (_ : Unit) (y x : Bool) : Prop := y = false ∧ x = true
def demiurgeCause (c x : Bool) (_ : Unit) : Prop := c = false ∧ x = true

/-- An exceeded god holds with the other premises of
`StageTwo.GodIsSimple.godIsSimple`, and something that is God is composite. -/
def ExceededGodSurvives : Prop :=
  SomeGodExceededInBeing demiurgeGod demiurgeAct demiurgeMore () ∧
    CompositeHasAUnitingCauseReading demiurgeGod demiurgeCause () ∧
    CauseOfQualityInAnotherIsMoreSuchReading demiurgeCause demiurgeMore ∧
    ¬ GodIsSimple demiurgeGod demiurgeGod

/-- A whole and two world-bound parts. -/
inductive Part where
  | whole | here | there
  deriving DecidableEq

/-- Two mutually accessible worlds. The whole exists at both; `here` exists at
the selected world `false` only and `there` at `true` only. At `false` the whole
grounds `here`; at `true`, `there` grounds the whole. -/
def sustainedWhole : Profile Bool Part where
  ontic := { frame := ⟨fun _ _ => True⟩,
             ExistsAt := fun w b => b = .whole ∨ (b = .here ∧ w = false) ∨ (b = .there ∧ w = true),
             Causes := fun _ _ _ => False }
  concrete := fun _ => True  -- category-constant: intended (all-concrete inventory: the model tests cross-world support, not the concrete/abstract line)
  grounds := fun v a b => (v = false ∧ a = .whole ∧ b = .here) ∨ (v = true ∧ a = .there ∧ b = .whole)

/-- Contingent support of a necessary concretum holds with the other premises of
`NecessaryConcreteUnderived.checks`, and no necessary concretum is underived at
every admitted world. -/
def ContingentSupportSurvives : Prop :=
  SomeNecessaryConcretumContingentlySupported sustainedWhole false ∧
    InhabitedConcreteAt sustainedWhole.ontic sustainedWhole.concrete false ∧
    ActualGroundingWF sustainedWhole false ∧
    EveryContingentGroundedAt sustainedWhole false ∧
    ActualReflexive sustainedWhole.ontic false ∧
    ConcreteNecessaryUnionWF sustainedWhole false ∧ ExcludedMiddle ∧
    ¬ NecessaryConcreteUnderivedAt sustainedWhole false

/-- Two mutually accessible worlds, two candidates existing at both. At the
selected world `false`, `false` grounds `true`; at `true`, `true` grounds
`false`. -/
def mutualPair : Profile Bool Bool where
  ontic := { frame := ⟨fun _ _ => True⟩, ExistsAt := fun _ _ => True, Causes := fun _ _ _ => False }
  concrete := fun _ => True  -- category-constant: intended (all-concrete inventory: the model tests cross-world support, not the concrete/abstract line)
  grounds := fun v a b => (v = false ∧ a = false ∧ b = true) ∨ (v = true ∧ a = true ∧ b = false)

/-- Mutual support of necessary concreta holds with the other premises of
`NecessaryConcreteUnderived.checks`, and no necessary concretum is underived at
every admitted world. -/
def MutualSupportSurvives : Prop :=
  NecessaryConcretaMutualSupport mutualPair false ∧
    InhabitedConcreteAt mutualPair.ontic mutualPair.concrete false ∧
    ActualGroundingWF mutualPair false ∧
    EveryContingentGroundedAt mutualPair false ∧
    ActualReflexive mutualPair.ontic false ∧
    NoContingentConcreteSupport mutualPair false ∧ ExcludedMiddle ∧
    ¬ NecessaryConcreteUnderivedAt mutualPair false

end Control

end TruthCore.Causality.SpineRivalsRootEsse
