module

public import TruthCore.Causality.FiniteBranching
public import TruthCore.Alternatives.ActPotencyRegress
public import TruthCore.Greek.Aristotle.Physics
public import TruthCore.Causality.CausalMapsBatch1
public import TruthCore.Case.Catholicism.StageOneQuartaVia
public import TruthCore.Causality.SelfOperationLife
public import TruthCore.Causality.LifeBoundaryPotency
public import TruthCore.Causality.SuccessionPotency
public import TruthCore.Causality.IntellectualInclination

/-!
# Round 5: worklist clusters (causal history, life, will)

Open analyst premises for derivations of eleven root-path statements that the
derivation worklist (`corpus.py thickness --queue`) lists without a verified
non-transcription derivation:

* map `explorations/round5-causal-history-priority.toml`: the three structural
  conditions of the finite-causal-history route, `NoCausalLoops`,
  `WellFoundedPredecessors` and `FiniteImmediatePredecessors`, from the simple
  priority of efficient causes and from Aristotle's four modes of cause; and
  `SimplyPriorIsCauseOfBeing` from the dependence reading of simple priority;
* map `explorations/round5-life-operation-change.toml`: `PureActOperates`,
  `SelfOperatingUnmovedLives`, `ImmutableHasNoLifeBoundary` and
  `SuccessionIsBeingMoved`, through operation following being in act and a typed
  relation of change between two times;
* map `explorations/round5-will-intelligible-form.toml`: the three q.19 a.1
  premises `EveryFormHasInclination`, `IntellectHasIntelligibleForm` and
  `IntelligibleInclinationIsWill`, through operation for an end, understanding,
  and an appetitive power following intellect.

Every definition below is an OPEN analyst formulation with attribution
deferred. New predicate parameters: `ChangesBetween x r t₁ t₂` (x changes in
respect r between times t₁ and t₂; `DEF-CHANGE-BETWEEN-TIMES`), `OperationOf o x`
(o is an operation of x; `DEF-OPERATION-OF`), `OperatesFromItselfAt x t`
(`DEF-OPERATES-FROM-ITSELF-AT`), `OperatesThrough x f o` and `DirectedTo o e`
(`DEF-OPERATION-THROUGH-FORM-FOR-END`), `Understands x q`
(`DEF-UNDERSTANDS`), `AppetitivePowerOf p x` and `FollowsIntellect p`
(`DEF-APPETITIVE-POWER-FOLLOWING-INTELLECT`). None is a modern notion
re-labelled: each is a parameter constrained only by the premises that use it.
-/

@[expose] public section

namespace TruthCore.Causality.Round5Worklist

open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism.StageOne.CausalFinitism
open TruthCore.Causality.FiniteBranching

variable {B R T S O F Q E P : Type}

/-! ## Map 1: causal history and priority -/

/-- OPEN bridge: every edge of the causal relation whose history is studied is an
efficient causing in some respect. It identifies the finite-history relation
with (a part of) efficient causation, the converse of
`PerSeLinksIncluded`; a history relation that also records material or
final dependence, or mere temporal succession, falsifies it. -/
def HistoryEdgesAreEfficientCausings (cause : B → B → Prop)
    (EfficientlyCausesIn : B → B → R → Prop) : Prop :=
  ∀ y x, cause y x → ∃ r, EfficientlyCausesIn y x r

/-- OPEN, contested: simple priority is well-founded, so there is no infinite
descending chain of beings each simply prior to the one before. Whoever admits
an infinite essentially ordered series denies it; it does not bound the length
of priority chains. -/
def SimplePriorityWellFounded (PriorSimply : B → B → Prop) : Prop :=
  WellFounded PriorSimply

/-- OPEN, contested: for each effect and each of Aristotle's four modes, the
effect has finitely many causes in that mode. An effect with infinitely many
material parts, or infinitely many concurring agents, falsifies it. -/
def FinitelyManyCausesPerMode (Material Formal SourceOfChange Final : B → B → Prop) :
    Prop :=
  ∀ x, {y | Material y x}.Finite ∧ {y | Formal y x}.Finite ∧
    {y | SourceOfChange y x}.Finite ∧ {y | Final y x}.Finite

/-- OPEN, contested: what a thing depends on for its being is a cause of its
being. A non-causal dependence for being (a set on its members, a fact on its
ground, on views that separate grounding from causation) falsifies it. -/
def DependenceForBeingIsCausedBeing (DependsForBeing : B → B → Prop)
    (CausesIn : B → B → R → Prop) (esse : R) : Prop :=
  ∀ x y, DependsForBeing x y → CausesIn y x esse

/-! ## Map 2: life, operation and change -/

/-- OPEN division in the respect of being: each being is in act or in potency in
its being (esse). It is silent on other respects and does not exclude both. -/
def ActOrPotencyInBeing (InAct InPotency : B → R → Prop) (esse : R) : Prop :=
  ∀ x, InAct x esse ∨ InPotency x esse

/-- OPEN (operation follows being): whatever is in act in its being has some
operation. A wholly inert actual being falsifies it. -/
def BeingInActHasOperation (InAct : B → R → Prop) (OperationOf : O → B → Prop)
    (esse : R) : Prop :=
  ∀ x, InAct x esse → ∃ o, OperationOf o x

/-- OPEN dichotomy, read from q.18 a.3 co. (things operate from themselves or as
moved by others): whatever has an operation either operates from itself or is
being moved in some respect. -/
def OperationFromSelfOrAsMoved (OperationOf : O → B → Prop) (Operates : B → Prop)
    (MovedIn : B → R → Prop) : Prop :=
  ∀ o x, OperationOf o x → Operates x ∨ ∃ r, MovedIn x r

/-- OPEN: an operation from itself is present at some time of the duration frame
(for what is not in time, read with q.10 a.2 ad 4). -/
def SelfOperationPresentAtSomeTime (Operates : B → Prop) (OperatesFromItselfAt : B → T → Prop) :
    Prop :=
  ∀ x, Operates x → ∃ t, OperatesFromItselfAt x t

/-- OPEN, q.18 a.2 reading (to live is the being of what operates from itself):
whatever operates from itself at a time lives at that time. -/
def OperatingFromItselfIsLiving (OperatesFromItselfAt LivesAt : B → T → Prop) : Prop :=
  ∀ x t, OperatesFromItselfAt x t → LivesAt x t

/-- OPEN, q.9 a.1 read for potency in the subject: whatever changes in a respect
between two times is in potency in that respect. The potency-in-another reading
(q.9 a.2, `DISAMB-POTENCY-IN-SUBJECT-VS-IN-ANOTHER`) would not give it. -/
def ChangeRequiresPotencyInSubject (ChangesBetween : B → R → T → T → Prop)
    (InPotency : B → R → Prop) : Prop :=
  ∀ x r t₁ t₂, ChangesBetween x r t₁ t₂ → InPotency x r

/-- OPEN: beginning or ceasing to live between an earlier and a later time is a
change of the living thing in some respect between them. Whoever denies that
generation or creation is a change of the thing generated denies it. -/
def LifeBoundaryIsChange [LT T] (LivesAt : B → T → Prop)
    (ChangesBetween : B → R → T → T → Prop) : Prop :=
  ∀ x t₁ t₂, t₁ < t₂ → ¬ (LivesAt x t₁ ↔ LivesAt x t₂) → ∃ r, ChangesBetween x r t₁ t₂

/-- OPEN: a difference of life-state between an earlier and a later time is a
change of the thing in some respect between them. -/
def StateDifferenceIsChange [LT T] (lifeStateAt : B → T → S)
    (ChangesBetween : B → R → T → T → Prop) : Prop :=
  ∀ x t₁ t₂, t₁ < t₂ → lifeStateAt x t₁ ≠ lifeStateAt x t₂ → ∃ r, ChangesBetween x r t₁ t₂

/-- OPEN, Physics V.1 reading: a change in a respect of a subject that is present
(lives) at both ends is a being moved in that respect, not generation or
corruption. `MovedIn` is untimed, as in `SuccessionIsBeingMoved`. -/
def ChangeOfPersistingSubjectIsMotion (LivesAt : B → T → Prop)
    (ChangesBetween : B → R → T → T → Prop) (MovedIn : B → R → Prop) : Prop :=
  ∀ x r t₁ t₂, ChangesBetween x r t₁ t₂ → LivesAt x t₁ → LivesAt x t₂ → MovedIn x r

/-! ## Map 3: will from intelligible form -/

/-- OPEN (form as principle of operation): every form a thing is in act through
is the principle of some operation of that thing through the form. -/
def FormIsPrincipleOfOperation (HasForm : B → F → Prop) (OperatesThrough : B → F → O → Prop) :
    Prop :=
  ∀ x f, HasForm x f → ∃ o, OperatesThrough x f o

/-- OPEN finality principle (*omne agens agit propter finem*), read for
operations through forms: every such operation is directed to some end. -/
def EveryOperationHasAnEnd (OperatesThrough : B → F → O → Prop) (DirectedTo : O → E → Prop) :
    Prop :=
  ∀ x f o, OperatesThrough x f o → ∃ e, DirectedTo o e

/-- OPEN recognition: a thing operating through a form toward an end has an
inclination following that form. -/
def EndDirectedOperationIsInclination (OperatesThrough : B → F → O → Prop)
    (DirectedTo : O → E → Prop) (InclinedTo : B → F → Prop) : Prop :=
  ∀ x f o e, OperatesThrough x f o → DirectedTo o e → InclinedTo x f

/-- OPEN, contested: whatever has intellect actually understands something. A
human intellect before any act of understanding (the possible intellect as a
*tabula rasa*, q.79 a.2) falsifies it. -/
def IntellectUnderstandsSomething (HasIntellect : B → Prop) (Understands : B → Q → Prop) :
    Prop :=
  ∀ x, HasIntellect x → ∃ q, Understands x q

/-- OPEN (q.14 a.2, q.85 a.2 reading): whatever understands something is in act
through some intelligible form. -/
def UnderstandingIsThroughIntelligibleForm (Understands : B → Q → Prop)
    (HasForm : B → F → Prop) (Intelligible : F → Prop) : Prop :=
  ∀ x q, Understands x q → ∃ f, Intelligible f ∧ HasForm x f

/-- OPEN (q.80 a.1–2 reading): an inclination following an intelligible form
belongs to some appetitive principle of the thing that follows intellectual
apprehension. "Power" is a principle; no real distinction from the essence is
asserted (`DISAMB-CREATURE-PASSIVE-APPETITE-AND-DIVINE-WILL`). -/
def IntelligibleInclinationIsIntellectualAppetite (Intelligible : F → Prop)
    (InclinedTo : B → F → Prop) (AppetitivePowerOf : P → B → Prop)
    (FollowsIntellect : P → Prop) : Prop :=
  ∀ x f, Intelligible f → InclinedTo x f → ∃ p, AppetitivePowerOf p x ∧ FollowsIntellect p

/-- OPEN (q.80 a.2, q.82 reading of `DEF-HAS-WILL`): whatever has an appetitive
principle following intellect has will. -/
def IntellectualAppetiteIsWill (AppetitivePowerOf : P → B → Prop) (FollowsIntellect : P → Prop)
    (HasWill : B → Prop) : Prop :=
  ∀ p x, AppetitivePowerOf p x → FollowsIntellect p → HasWill x

/-! ## Controls

Finite interpretations (infinite `ℕ` only where finiteness is the point). Each
`omit…` makes one premise of one derivation fail, the others hold, and the
conclusion fail; `witness…` makes every premise and conclusion of a map hold
with populated antecedents. Satisfiability and omission only. -/

namespace Control
open TruthCore.Alternatives.ActPotencyRegress (SimplePriorityTransitiveReading)
open TruthCore.Greek.Aristotle.Physics (FourCauseExhaustiveReading)
open TruthCore.Causality.CausalMapsBatch1 (PriorityRequiresNonmutualDependence)
open TruthCore.Case.Catholicism (SimplyPriorIsCauseOfBeing)
open TruthCore.Causality.SelfOperationLife
open TruthCore.Causality.LifeBoundaryPotency
open TruthCore.Causality.SuccessionPotency
open TruthCore.Causality.IntellectualInclination

def t2 (_ _ : Unit) : Prop := True
def f2 (_ _ : Unit) : Prop := False
def t3 (_ _ _ : Unit) : Prop := True
def f3 (_ _ _ : Unit) : Prop := False
def neB (y x : Bool) : Prop := y ≠ x
def downB (y x : Bool) : Prop := y = false ∧ x = true

/-! ### Map 1 -/

/-- `noLoopsFromPriority`, omit the edge bridge: a self-loop that is no efficient causing. -/
def omitEdgesLoops : Prop :=
  ¬ HistoryEdgesAreEfficientCausings t2 (fun (_ _ _ : Unit) => False) ∧
    EfficientCauseIsPriorToEffectReading (fun (_ _ _ : Unit) => False) f2 ∧
    SimplePriorityTransitiveReading f2 ∧ NothingPriorToItselfReading f2 ∧
    ¬ NoCausalLoops t2

/-- `noLoopsFromPriority`, omit efficient-cause priority. -/
def omitPriorLoops : Prop :=
  HistoryEdgesAreEfficientCausings t2 t3 ∧
    ¬ EfficientCauseIsPriorToEffectReading t3 f2 ∧
    SimplePriorityTransitiveReading f2 ∧ NothingPriorToItselfReading f2 ∧
    ¬ NoCausalLoops t2

/-- `noLoopsFromPriority`, omit transitivity: a two-cycle on `Bool` whose
priority is irreflexive but not transitive. -/
def omitTransLoops : Prop :=
  HistoryEdgesAreEfficientCausings neB (fun (y x : Bool) (_ : Unit) => neB y x) ∧
    EfficientCauseIsPriorToEffectReading (fun (y x : Bool) (_ : Unit) => neB y x) neB ∧
    ¬ SimplePriorityTransitiveReading neB ∧ NothingPriorToItselfReading neB ∧
    ¬ NoCausalLoops neB

/-- `noLoopsFromPriority`, omit irreflexivity. -/
def omitIrreflLoops : Prop :=
  HistoryEdgesAreEfficientCausings t2 t3 ∧
    EfficientCauseIsPriorToEffectReading t3 t2 ∧
    SimplePriorityTransitiveReading t2 ∧ ¬ NothingPriorToItselfReading t2 ∧
    ¬ NoCausalLoops t2

/-- `wellFoundedFromPriority`, omit the edge bridge. -/
def omitEdgesWF : Prop :=
  ¬ HistoryEdgesAreEfficientCausings t2 (fun (_ _ _ : Unit) => False) ∧
    EfficientCauseIsPriorToEffectReading (fun (_ _ _ : Unit) => False) f2 ∧
    SimplePriorityWellFounded f2 ∧ ¬ WellFoundedPredecessors t2

/-- `wellFoundedFromPriority`, omit efficient-cause priority. -/
def omitPriorWF : Prop :=
  HistoryEdgesAreEfficientCausings t2 t3 ∧
    ¬ EfficientCauseIsPriorToEffectReading t3 f2 ∧
    SimplePriorityWellFounded f2 ∧ ¬ WellFoundedPredecessors t2

/-- `wellFoundedFromPriority`, omit well-founded priority. -/
def omitWFPriority : Prop :=
  HistoryEdgesAreEfficientCausings t2 t3 ∧
    EfficientCauseIsPriorToEffectReading t3 t2 ∧
    ¬ SimplePriorityWellFounded t2 ∧ ¬ WellFoundedPredecessors t2

/-- `finitePredecessorsFromModes`, omit the four-cause classification: every
number causes every number in no mode. -/
def omitFourModes : Prop :=
  ¬ FourCauseExhaustiveReading (fun (_ _ : ℕ) => True) (fun _ _ => False) (fun _ _ => False)
      (fun _ _ => False) (fun _ _ => False) ∧
    FinitelyManyCausesPerMode (fun (_ _ : ℕ) => False) (fun _ _ => False) (fun _ _ => False)
      (fun _ _ => False) ∧
    ¬ FiniteImmediatePredecessors (fun (_ _ : ℕ) => True)

/-- `finitePredecessorsFromModes`, omit finitely many causes per mode: infinitely
many material causes. -/
def omitFinitePerMode : Prop :=
  FourCauseExhaustiveReading (fun (_ _ : ℕ) => True) (fun _ _ => True) (fun _ _ => False)
      (fun _ _ => False) (fun _ _ => False) ∧
    ¬ FinitelyManyCausesPerMode (fun (_ _ : ℕ) => True) (fun _ _ => False) (fun _ _ => False)
      (fun _ _ => False) ∧
    ¬ FiniteImmediatePredecessors (fun (_ _ : ℕ) => True)

/-- `simplyPriorCausesBeing`, omit the dependence reading of priority: priority
without dependence. -/
def omitPriorityDependence : Prop :=
  ¬ PriorityRequiresNonmutualDependence t2 f2 ∧
    DependenceForBeingIsCausedBeing f2 f3 () ∧
    ¬ SimplyPriorIsCauseOfBeing t2 f3 ()

/-- `simplyPriorCausesBeing`, omit dependence-as-causation: `true` is prior to
`false`, which depends on it, without causing its being. -/
def omitDependenceCausation : Prop :=
  PriorityRequiresNonmutualDependence (fun y x : Bool => y = true ∧ x = false)
      (fun x y : Bool => x = false ∧ y = true) ∧
    ¬ DependenceForBeingIsCausedBeing (fun x y : Bool => x = false ∧ y = true)
      (fun (_ _ : Bool) (_ : Unit) => False) () ∧
    ¬ SimplyPriorIsCauseOfBeing (fun y x : Bool => y = true ∧ x = false)
      (fun (_ _ : Bool) (_ : Unit) => False) ()

/-- Joint witness for map 1: `false` efficiently causes `true`, is simply prior to
it, is its source of change, and is depended on by it for being and causes its
being. -/
def witnessHistory : Prop :=
  HistoryEdgesAreEfficientCausings downB (fun (y x : Bool) (_ : Unit) => downB y x) ∧
    EfficientCauseIsPriorToEffectReading (fun (y x : Bool) (_ : Unit) => downB y x) downB ∧
    SimplePriorityTransitiveReading downB ∧ NothingPriorToItselfReading downB ∧
    SimplePriorityWellFounded downB ∧
    FourCauseExhaustiveReading downB (fun _ _ => False) (fun _ _ => False) downB
      (fun _ _ => False) ∧
    FinitelyManyCausesPerMode (fun (_ _ : Bool) => False) (fun _ _ => False) downB
      (fun _ _ => False) ∧
    PriorityRequiresNonmutualDependence downB (fun x y => downB y x) ∧
    DependenceForBeingIsCausedBeing (fun x y => downB y x) (fun (y x : Bool) (_ : Unit) => downB y x) () ∧
    NoCausalLoops downB ∧ WellFoundedPredecessors downB ∧ FiniteImmediatePredecessors downB ∧
    SimplyPriorIsCauseOfBeing downB (fun (y x : Bool) (_ : Unit) => downB y x) () ∧
    downB false true

/-! ### Map 2 (one being `()`, respects `Unit`, times `Fin 2` with `0 < 1`) -/

/-- `pureActOperatesFromBeing`, omit the act/potency division. -/
def omitDivision : Prop :=
  ¬ ActOrPotencyInBeing f2 f2 () ∧ BeingInActHasOperation f2 f2 () ∧
    OperationFromSelfOrAsMoved f2 (fun _ => False) f2 ∧ MovedOnlyAsInPotencyReading f2 f2 ∧
    ¬ PureActOperates f2 (fun _ => False)

/-- `pureActOperatesFromBeing`, omit operation following being in act: an inert
pure act. -/
def omitOperationFollows : Prop :=
  ActOrPotencyInBeing t2 f2 () ∧ ¬ BeingInActHasOperation t2 f2 () ∧
    OperationFromSelfOrAsMoved f2 (fun _ => False) f2 ∧ MovedOnlyAsInPotencyReading f2 f2 ∧
    ¬ PureActOperates f2 (fun _ => False)

/-- `pureActOperatesFromBeing`, omit the dichotomy. -/
def omitSelfOrMoved : Prop :=
  ActOrPotencyInBeing t2 f2 () ∧ BeingInActHasOperation t2 t2 () ∧
    ¬ OperationFromSelfOrAsMoved t2 (fun _ => False) f2 ∧ MovedOnlyAsInPotencyReading f2 f2 ∧
    ¬ PureActOperates f2 (fun _ => False)

/-- `pureActOperatesFromBeing`, omit q.2 a.3: a pure act that is moved. -/
def omitMovedPotency : Prop :=
  ActOrPotencyInBeing t2 f2 () ∧ BeingInActHasOperation t2 t2 () ∧
    OperationFromSelfOrAsMoved t2 (fun _ => False) t2 ∧ ¬ MovedOnlyAsInPotencyReading t2 f2 ∧
    ¬ PureActOperates f2 (fun _ => False)

/-- `selfOperatingUnmovedLivesFromOperation`, omit presence of self-operation. -/
def omitPresent : Prop :=
  ¬ SelfOperationPresentAtSomeTime (fun (_ : Unit) => True) (fun (_ : Unit) (_ : Fin 2) => False) ∧
    OperatingFromItselfIsLiving (fun (_ : Unit) (_ : Fin 2) => False) (fun _ _ => False) ∧
    ¬ SelfOperatingUnmovedLives (fun (_ : Unit) => True) f2 (fun (_ : Unit) (_ : Fin 2) => False)

/-- `selfOperatingUnmovedLivesFromOperation`, omit self-operation as life. -/
def omitLiving : Prop :=
  SelfOperationPresentAtSomeTime (fun (_ : Unit) => True) (fun (_ : Unit) (_ : Fin 2) => True) ∧
    ¬ OperatingFromItselfIsLiving (fun (_ : Unit) (_ : Fin 2) => True) (fun _ _ => False) ∧
    ¬ SelfOperatingUnmovedLives (fun (_ : Unit) => True) f2 (fun (_ : Unit) (_ : Fin 2) => False)

/-- Life that begins at time `1`. -/
def begins (_ : Unit) (t : Fin 2) : Prop := t = 1

/-- `noLifeBoundaryFromChange`, omit the boundary-as-change premise. -/
def omitBoundaryChange : Prop :=
  ¬ LifeBoundaryIsChange begins (fun (_ _ : Unit) (_ _ : Fin 2) => False) ∧
    ChangeRequiresPotencyInSubject (fun (_ _ : Unit) (_ _ : Fin 2) => False) f2 ∧
    ¬ ImmutableHasNoLifeBoundary f2 begins

/-- `noLifeBoundaryFromChange`, omit q.9 a.1 (potency in the subject). -/
def omitChangePotency : Prop :=
  LifeBoundaryIsChange begins (fun (_ _ : Unit) (_ _ : Fin 2) => True) ∧
    ¬ ChangeRequiresPotencyInSubject (fun (_ _ : Unit) (_ _ : Fin 2) => True) f2 ∧
    ¬ ImmutableHasNoLifeBoundary f2 begins

/-- Life at both times with state `t`. -/
def livesB (_ : Unit) (_ : Fin 2) : Prop := True
def stateB (_ : Unit) (t : Fin 2) : Fin 2 := t

/-- `successionMotionFromChange`, omit state difference as change. -/
def omitStateChange : Prop :=
  ¬ StateDifferenceIsChange stateB (fun (_ _ : Unit) (_ _ : Fin 2) => False) ∧
    ChangeOfPersistingSubjectIsMotion livesB (fun (_ _ : Unit) (_ _ : Fin 2) => False) f2 ∧
    ¬ SuccessionIsBeingMoved livesB stateB f2

/-- `successionMotionFromChange`, omit Physics V.1 (change of a persisting
subject is motion). -/
def omitPersistingMotion : Prop :=
  StateDifferenceIsChange stateB (fun (_ _ : Unit) (_ _ : Fin 2) => True) ∧
    ¬ ChangeOfPersistingSubjectIsMotion livesB (fun (_ _ : Unit) (_ _ : Fin 2) => True) f2 ∧
    ¬ SuccessionIsBeingMoved livesB stateB f2

/-- Joint witness for map 2, with two beings: `false` is a pure act, in act in
being, with an operation from itself, living at every time with a constant
state; `true` is in potency in being and is moved, changes in every respect
between the two times, and lives at both with different states. -/
def witnessLife : Prop :=
  ActOrPotencyInBeing (fun (x : Bool) (_ : Unit) => x = false) (fun x _ => x = true) () ∧
    BeingInActHasOperation (fun (x : Bool) (_ : Unit) => x = false) (fun (_ : Unit) x => x = false) () ∧
    OperationFromSelfOrAsMoved (fun (_ : Unit) (x : Bool) => x = false) (fun x => x = false)
      (fun x (_ : Unit) => x = true) ∧
    MovedOnlyAsInPotencyReading (fun (x : Bool) (_ : Unit) => x = true) (fun x _ => x = true) ∧
    PureActOperates (fun (x : Bool) (_ : Unit) => x = true) (fun x => x = false) ∧
    SelfOperationPresentAtSomeTime (fun (x : Bool) => x = false) (fun x (_ : Fin 2) => x = false) ∧
    OperatingFromItselfIsLiving (fun (x : Bool) (_ : Fin 2) => x = false) (fun _ _ => True) ∧
    SelfOperatingUnmovedLives (fun (x : Bool) => x = false) (fun x (_ : Unit) => x = true)
      (fun _ (_ : Fin 2) => True) ∧
    LifeBoundaryIsChange (fun (_ : Bool) (_ : Fin 2) => True)
      (fun (x : Bool) (_ : Unit) (_ _ : Fin 2) => x = true) ∧
    ChangeRequiresPotencyInSubject (fun (x : Bool) (_ : Unit) (_ _ : Fin 2) => x = true)
      (fun x _ => x = true) ∧
    ImmutableHasNoLifeBoundary (fun (x : Bool) (_ : Unit) => x = true) (fun _ (_ : Fin 2) => True) ∧
    StateDifferenceIsChange (fun (x : Bool) (t : Fin 2) => if x then t else 0)
      (fun (x : Bool) (_ : Unit) (_ _ : Fin 2) => x = true) ∧
    ChangeOfPersistingSubjectIsMotion (fun (_ : Bool) (_ : Fin 2) => True)
      (fun (x : Bool) (_ : Unit) (_ _ : Fin 2) => x = true) (fun x _ => x = true) ∧
    SuccessionIsBeingMoved (fun (_ : Bool) (_ : Fin 2) => True) (fun (x : Bool) (t : Fin 2) => if x then t else 0)
      (fun (x : Bool) (_ : Unit) => x = true) ∧
    PureAct (fun (x : Bool) (_ : Unit) => x = true) false ∧
    LifeHasSuccession (fun (_ : Bool) (_ : Fin 2) => True) (fun (x : Bool) (t : Fin 2) => if x then t else 0) true ∧
    -- the boundary premises with a populated antecedent: `true` begins to live
    LifeBoundaryIsChange (fun (x : Bool) (t : Fin 2) => x = false ∨ t = 1)
      (fun (x : Bool) (_ : Unit) (_ _ : Fin 2) => x = true) ∧
    ImmutableHasNoLifeBoundary (fun (x : Bool) (_ : Unit) => x = true)
      (fun (x : Bool) (t : Fin 2) => x = false ∨ t = 1) ∧
    LifeBeginsOrEnds (fun (x : Bool) (t : Fin 2) => x = false ∨ t = 1) true

/-! ### Map 3 (one being `()`, forms `Unit`) -/

/-- `everyFormInclinedFromFinality`, omit form as principle of operation. -/
def omitFormPrinciple : Prop :=
  ¬ FormIsPrincipleOfOperation t2 f3 ∧ EveryOperationHasAnEnd f3 f2 ∧
    EndDirectedOperationIsInclination f3 f2 f2 ∧ ¬ EveryFormHasInclination t2 f2

/-- `everyFormInclinedFromFinality`, omit the finality principle. -/
def omitFinality : Prop :=
  FormIsPrincipleOfOperation t2 t3 ∧ ¬ EveryOperationHasAnEnd t3 f2 ∧
    EndDirectedOperationIsInclination t3 f2 f2 ∧ ¬ EveryFormHasInclination t2 f2

/-- `everyFormInclinedFromFinality`, omit the inclination recognition. -/
def omitEndInclination : Prop :=
  FormIsPrincipleOfOperation t2 t3 ∧ EveryOperationHasAnEnd t3 t2 ∧
    ¬ EndDirectedOperationIsInclination t3 t2 f2 ∧ ¬ EveryFormHasInclination t2 f2

/-- `intellectFormFromUnderstanding`, omit actual understanding: an intellect
that understands nothing (a *tabula rasa*). -/
def omitUnderstandsSomething : Prop :=
  ¬ IntellectUnderstandsSomething (fun (_ : Unit) => True) f2 ∧
    UnderstandingIsThroughIntelligibleForm f2 f2 (fun _ => True) ∧
    ¬ IntellectHasIntelligibleForm (fun (_ : Unit) => True) f2 (fun (_ : Unit) => True)

/-- `intellectFormFromUnderstanding`, omit understanding through intelligible form. -/
def omitThroughForm : Prop :=
  IntellectUnderstandsSomething (fun (_ : Unit) => True) t2 ∧
    ¬ UnderstandingIsThroughIntelligibleForm t2 f2 (fun _ => True) ∧
    ¬ IntellectHasIntelligibleForm (fun (_ : Unit) => True) f2 (fun (_ : Unit) => True)

/-- `willFromIntellectualAppetite`, omit the appetite reading of intelligible
inclination. -/
def omitAppetite : Prop :=
  ¬ IntelligibleInclinationIsIntellectualAppetite (fun (_ : Unit) => True) t2 f2 (fun _ => True) ∧
    IntellectualAppetiteIsWill f2 (fun _ => True) (fun _ => False) ∧
    ¬ IntelligibleInclinationIsWill (fun (_ : Unit) => True) t2 (fun _ => False)

/-- `willFromIntellectualAppetite`, omit intellectual appetite as will. -/
def omitAppetiteWill : Prop :=
  IntelligibleInclinationIsIntellectualAppetite (fun (_ : Unit) => True) t2 t2 (fun _ => True) ∧
    ¬ IntellectualAppetiteIsWill t2 (fun _ => True) (fun _ => False) ∧
    ¬ IntelligibleInclinationIsWill (fun (_ : Unit) => True) t2 (fun _ => False)

/-- Joint witness for map 3: one intellectual being, one intelligible form, its
operation for an end, its inclination, appetite and will. -/
def witnessWill : Prop :=
  FormIsPrincipleOfOperation t2 t3 ∧ EveryOperationHasAnEnd t3 t2 ∧
    EndDirectedOperationIsInclination t3 t2 t2 ∧ EveryFormHasInclination t2 t2 ∧
    IntellectUnderstandsSomething (fun (_ : Unit) => True) t2 ∧
    UnderstandingIsThroughIntelligibleForm t2 t2 (fun (_ : Unit) => True) ∧
    IntellectHasIntelligibleForm (fun (_ : Unit) => True) t2 (fun (_ : Unit) => True) ∧
    IntelligibleInclinationIsIntellectualAppetite (fun (_ : Unit) => True) t2 t2 (fun (_ : Unit) => True) ∧
    IntellectualAppetiteIsWill t2 (fun _ => True) (fun (_ : Unit) => True) ∧
    IntelligibleInclinationIsWill (fun (_ : Unit) => True) t2 (fun _ => True)

/-- The batch controls: one omission model per premise of each derivation and one
joint nonvacuity witness per map. -/
def Certificate : Prop :=
  omitEdgesLoops ∧ omitPriorLoops ∧ omitTransLoops ∧ omitIrreflLoops ∧
    omitEdgesWF ∧ omitPriorWF ∧ omitWFPriority ∧
    omitFourModes ∧ omitFinitePerMode ∧
    omitPriorityDependence ∧ omitDependenceCausation ∧ witnessHistory ∧
    omitDivision ∧ omitOperationFollows ∧ omitSelfOrMoved ∧ omitMovedPotency ∧
    omitPresent ∧ omitLiving ∧ omitBoundaryChange ∧ omitChangePotency ∧
    omitStateChange ∧ omitPersistingMotion ∧ witnessLife ∧
    omitFormPrinciple ∧ omitFinality ∧ omitEndInclination ∧
    omitUnderstandsSomething ∧ omitThroughForm ∧ omitAppetite ∧ omitAppetiteWill ∧ witnessWill

end Control
end TruthCore.Causality.Round5Worklist
