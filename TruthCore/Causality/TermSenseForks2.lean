module

public import TruthCore.Causality.TermSenseForks
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article7Uniting
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article7Cause
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4
public import TruthCore.Causality.ComponentFirstness

/-! Sense forks, batch 2: "uniting cause", "in act" and "cause of becoming or being"

Owner direction (sense-indexed terms): senses carry labels TERM_n in the order
of the disambiguation's `sense_definition_ids`, and an argument that works
under several senses is recorded as one argument per sense (ID suffix
-TERM-n). The per-sense theorems below are the primary results; the joint
theorems over the enums are optional summaries.

Analyst formulations, attribution deferred. Continues `TermSenseForks` and
reuses its generic coverage (`SensesCover`), exclusivity (`SenseUnique`) and
uses-agree vocabulary (DEF-ROUTE-SENSE-SELECTION).

Here exclusivity feeds a root route directly. Each route below uses the forked
term twice, and its step is valid only if both uses are read in the same sense.
The joint theorems take coverage for both uses and exclusivity of the route's
reading, so the conclusion follows **whichever** single sense applies. The
controls give, for each term, a model of coverage without exclusivity in which
the two uses are read in different senses and the conclusion fails.

* **uniting cause** (DISAMB-UNITING-CAUSE). The third proof of ST I q.3 a.7
  needs the uniter `c` of a composite `x` to be distinct from `x`. The route
  says that the uniter causes `x` and that nothing causes itself; the senses of
  "causes" are efficient causing in some respect, causing `x`'s being
  (`CausesIn c x esse`) and uniting components into `x` (`Unites`). The
  existing route COMPOSITE-UNITING-CAUSE-FROM-UNION reads both uses as efficient.
  The temporal composer profile (DEF-COMPOSER-TEMPORAL-PROFILE) is a time
  calibration of the efficient sense and has its own checked fork, so it is not
  a further constructor here.
* **in act** (DISAMB-IN-ACT). The prima via's step to "nothing moves itself in
  the same respect" uses `InAct` twice: the mover is in act, and nothing is in
  act and in potency in the same respect. The senses are formal act, virtual
  (eminent) act, and the inclusive "formally or virtually" of ST I q.4 a.2
  (*univoce vel eminentius*). `InActFormally` and `InActVirtually` are new
  parameters for DEF-IN-ACT-FORMALLY and DEF-IN-ACT-VIRTUALLY, which had no
  Lean declaration; their disjointness (virtual act is "without having it in
  the same form") is not encoded, because no step needs it.

Exclusivity is again a constraint on the route's reading choice
(`Select`), not a disjointness claim about extensions. -/

@[expose] public section

namespace TruthCore.Causality.TermSenseForks

open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article7Uniting

/-! ## "uniting cause" -/

/-- The senses in which a uniter is said to cause the composite, labelled by
DISAMB-UNITING-CAUSE's sense order: UNITING-CAUSE_1 uniting (DEF-UNITING-CAUSE),
UNITING-CAUSE_2 efficient causing (DEF-EFFICIENT-CAUSING), UNITING-CAUSE_3
causing the composite's being (DEF-CAUSE-OF-PERFECTION at esse).
UNITING-CAUSE_4, the temporal composer profile, is a time calibration of
UNITING-CAUSE_2 with its own checked fork and is not a constructor here. -/
inductive UnitingSense
  | uniting
  | efficient
  | being
  deriving DecidableEq

/-- The two uses of "causes" in the uniting-cause step. -/
inductive UnitingUse
  | uniterCauses
  | noSelfCause
  deriving DecidableEq

/-- The parameters of the third proof of q.3 a.7. -/
structure UnitingFrame (Being : Type) (Respect : Type) where
  Unites : Being → Being → Being → Being → Prop
  EfficientlyCausesIn : Being → Being → Respect → Prop
  CausesIn : Being → Being → Respect → Prop
  esse : Respect

/-- The sense-relative relation "`c` causes `x`": efficient causing in some
respect, causing `x`'s being, or uniting some components into `x`. -/
def UnitingFrame.CausesBy {Being Respect : Type} (F : UnitingFrame Being Respect) :
    UnitingSense → Being → Being → Prop
  | .efficient => fun c x => ∃ r, F.EfficientlyCausesIn c x r
  | .being => fun c x => F.CausesIn c x F.esse
  | .uniting => fun c x => ∃ a b, F.Unites c a b x

/-- COVERAGE (STMT-UNITING-CAUSE-SENSES-EXHAUSTIVE): each use of "causes" in
the uniting-cause step is read in one of efficient causing, causing being, or
uniting, selected by the route's reading. OPEN frontier premise. -/
def UnitingCauseSensesExhaustive {Being Respect : Type} (F : UnitingFrame Being Respect)
    (Select : UnitingSense → Prop) (use : UnitingUse → Being → Being → Prop) : Prop :=
  SensesCover F.CausesBy Select use

/-- EXCLUSIVITY (STMT-UNITING-CAUSE-SENSE-UNIQUE): the route's reading of
"causes" in the uniting-cause step selects at most one sense. OPEN frontier
premise; not a disjointness claim. -/
def UnitingCauseSenseUnique (Select : UnitingSense → Prop) : Prop :=
  SenseUnique Select

/-- Whatever unites components into `x` causes `x`, in the route's reading of
the first use. -/
def UniterCausesInRouteSense {Being Respect : Type} (F : UnitingFrame Being Respect)
    (use : UnitingUse → Being → Being → Prop) : Prop :=
  ∀ c a b x, F.Unites c a b x → use .uniterCauses c x

/-- Nothing causes itself, in the route's reading of the second use. -/
def NothingCausesItselfInRouteUse {Being : Type}
    (use : UnitingUse → Being → Being → Prop) : Prop :=
  ∀ x, ¬ use .noSelfCause x x

/-- UNITING-CAUSE_3: nothing causes its own being (`CausesIn x x esse`): the
esse instance of STMT-NOTHING-CAUSES-ITS-OWN-PERFECTION. -/
def NothingCausesItsOwnBeing {Being Respect : Type}
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect) : Prop :=
  ∀ x, ¬ CausesIn x x esse

/-- UNITING-CAUSE_1: nothing unites components into itself. -/
def NothingUnitesItself {Being : Type}
    (Unites : Being → Being → Being → Being → Prop) : Prop :=
  ∀ x a b, ¬ Unites x a b x

/-! ## "in act" -/

/-- The senses of "in act", labelled by DISAMB-IN-ACT's sense order: IN-ACT_1
formally (DEF-IN-ACT-FORMALLY), IN-ACT_2 virtually or eminently
(DEF-IN-ACT-VIRTUALLY), IN-ACT_3 formally or virtually
(DEF-IN-ACT-FORMALLY-OR-VIRTUALLY, ST I q.4 a.2 *univoce vel eminentius*). -/
inductive ActSense
  | formally
  | virtually
  | formallyOrVirtually
  deriving DecidableEq

/-- The two uses of "in act" in the step to no self-motion. -/
inductive ActUse
  | moverInAct
  | nonSimultaneity
  deriving DecidableEq

/-- The parameters of the prima via step. -/
structure ActFrame (Being : Type) (Respect : Type) where
  /-- DEF-IN-ACT-FORMALLY. -/
  InActFormally : Being → Respect → Prop
  /-- DEF-IN-ACT-VIRTUALLY. -/
  InActVirtually : Being → Respect → Prop
  InPotency : Being → Respect → Prop
  MovedIn : Being → Respect → Prop
  MovesIn : Being → Being → Respect → Prop

/-- IN-ACT_3 (DEF-IN-ACT-FORMALLY-OR-VIRTUALLY): in act formally or virtually.
Its own declaration, so that IN-ACT_3 statements mention neither sense alone. -/
def ActFrame.InActFormallyOrVirtually {Being Respect : Type} (F : ActFrame Being Respect)
    (x : Being) (r : Respect) : Prop :=
  F.InActFormally x r ∨ F.InActVirtually x r

/-- The sense-indexed act predicate of the optional summary: each constructor
unfolds to its sense's own declaration (`InActFormally`, `InActVirtually`,
`InActFormallyOrVirtually`). Per-sense statements never use it. -/
def ActFrame.InActBy {Being Respect : Type} (F : ActFrame Being Respect) :
    ActSense → Being → Respect → Prop
  | .formally => F.InActFormally
  | .virtually => F.InActVirtually
  | .formallyOrVirtually => F.InActFormallyOrVirtually

/-- COVERAGE (STMT-IN-ACT-SENSES-EXHAUSTIVE): each use of "in act" in the step
is read as formal act, virtual act, or formal-or-virtual act, selected by the
route's reading. OPEN frontier premise. -/
def InActSensesExhaustive {Being Respect : Type} (F : ActFrame Being Respect)
    (Select : ActSense → Prop) (use : ActUse → Being → Respect → Prop) : Prop :=
  SensesCover F.InActBy Select use

/-- EXCLUSIVITY (STMT-IN-ACT-SENSE-UNIQUE): the route's reading of "in act"
selects at most one sense. OPEN frontier premise; not a disjointness claim. -/
def InActSenseUnique (Select : ActSense → Prop) : Prop :=
  SenseUnique Select

/-- IN-ACT_1: a thing moves only as formally in act. -/
def MovesOnlyAsFormallyInAct {Being Respect : Type} (F : ActFrame Being Respect) : Prop :=
  MovesOnlyAsInActReading F.MovesIn F.InActFormally

/-- IN-ACT_3: a thing moves only as in act formally or virtually. -/
def MovesOnlyAsInActFormallyOrVirtually {Being Respect : Type}
    (F : ActFrame Being Respect) : Prop :=
  MovesOnlyAsInActReading F.MovesIn F.InActFormallyOrVirtually

/-- IN-ACT_1: nothing is formally in act and in potency in the same respect. -/
def NothingFormallyInActAndInPotency {Being Respect : Type}
    (F : ActFrame Being Respect) : Prop :=
  NotActAndPotencyInSameRespectReading F.InActFormally F.InPotency

/-- IN-ACT_3: nothing is in act formally or virtually and in potency in the
same respect. -/
def NothingInActFormallyOrVirtuallyAndInPotency {Being Respect : Type}
    (F : ActFrame Being Respect) : Prop :=
  NotActAndPotencyInSameRespectReading F.InActFormallyOrVirtually F.InPotency

/-- IN-ACT_2: a thing moves only as virtually in act. -/
def MovesOnlyAsVirtuallyInAct {Being Respect : Type} (F : ActFrame Being Respect) : Prop :=
  MovesOnlyAsInActReading F.MovesIn F.InActVirtually

/-- IN-ACT_2: nothing is virtually in act and in potency in the same respect. -/
def NothingVirtuallyInActAndInPotency {Being Respect : Type}
    (F : ActFrame Being Respect) : Prop :=
  NotActAndPotencyInSameRespectReading F.InActVirtually F.InPotency

/-! ## "cause" of becoming and of being (DISAMB-BECOMING-BEING-CAUSE)

Senses in DISAMB-BECOMING-BEING-CAUSE's order: BECOMING-BEING-CAUSE_1 cause of
becoming (DEF-CAUSE-OF-BECOMING, here `CausesOrigin`), BECOMING-BEING-CAUSE_2
external cause of esse (DEF-EXTERNAL-CAUSE-OF-ESSE, the q.3 a.4
`HasExternalEsseCause`), BECOMING-BEING-CAUSE_3 cause of a perfection at esse
(DEF-CAUSE-OF-PERFECTION, `CausesIn c x esse`). The root-path statement
STMT-PARTICIPATED-HAS-OTHER-CAUSE is in sense 3. -/

/-- The parameters: a q.3 a.4 profile (whose `CausesIn` and `esse` are the
shared Aquinas vocabulary), a cause-of-becoming relation and participation. -/
structure BecomingBeingFrame (Being Principle Respect : Type) where
  profile : PrimaPars.Question3.Article4.Profile Being Principle Respect
  CausesOrigin : Being → Being → Prop
  Participated : Being → Prop

/-- OPEN analyst bridge: whatever has being by participation actually exists
with esse distinct from its essence. -/
def ParticipatedHasDistinctEsse {Being Principle Respect : Type}
    (F : BecomingBeingFrame Being Principle Respect) : Prop :=
  ∀ x, F.Participated x → PrimaPars.Question3.Article4.DistinctEsseAt F.profile x

/-- BECOMING-BEING-CAUSE_2: whatever has being by participation has an actually
existing external efficient cause of its esse. -/
def ParticipatedHasExternalEsseCause {Being Principle Respect : Type}
    (F : BecomingBeingFrame Being Principle Respect) : Prop :=
  ∀ x, F.Participated x → PrimaPars.Question3.Article4.HasExternalEsseCause F.profile x

/-- BECOMING-BEING-CAUSE_1: whatever has being by participation has a cause,
other than itself, of its coming to be. -/
def ParticipatedHasOtherCauseOfBecoming {Being Principle Respect : Type}
    (F : BecomingBeingFrame Being Principle Respect) : Prop :=
  ∀ x, F.Participated x → ∃ c, c ≠ x ∧ F.CausesOrigin c x

/-! ## Controls -/

/-- Controls of batch 2. -/
def TermSenseForks2Controls : Prop :=
  -- uniting: coverage without exclusivity; the uniter causes `x` as uniter,
  -- nothing is its own efficient cause, the only uniter is `x` itself
  (∃ (Composite : Bool → Prop) (ComponentOf : Bool → Bool → Prop)
      (F : UnitingFrame Bool Unit) (Select : UnitingSense → Prop)
      (use : UnitingUse → Bool → Bool → Prop),
    CompositeHasTwoDistinctComponentsReading Composite ComponentOf ∧
    DiverseUnitedOnlyThroughUnitingCauseReading ComponentOf F.Unites ∧
    UnitingCauseCausesBeingReading F.Unites F.CausesIn F.esse ∧
    UnitingCauseSensesExhaustive F Select use ∧ ¬ UnitingCauseSenseUnique Select ∧
    UniterCausesInRouteSense F use ∧ NothingCausesItselfInRouteUse use ∧
    ¬ CompositeHasAUnitingCauseReading Composite F.CausesIn F.esse) ∧
  -- uniting: coverage fails (uses outside every sense), the rest holds
  (∃ (Composite : Bool → Prop) (ComponentOf : Bool → Bool → Prop)
      (F : UnitingFrame Bool Unit) (Select : UnitingSense → Prop)
      (use : UnitingUse → Bool → Bool → Prop),
    CompositeHasTwoDistinctComponentsReading Composite ComponentOf ∧
    DiverseUnitedOnlyThroughUnitingCauseReading ComponentOf F.Unites ∧
    UnitingCauseCausesBeingReading F.Unites F.CausesIn F.esse ∧
    ¬ UnitingCauseSensesExhaustive F Select use ∧ UnitingCauseSenseUnique Select ∧
    UniterCausesInRouteSense F use ∧ NothingCausesItselfInRouteUse use ∧
    ¬ CompositeHasAUnitingCauseReading Composite F.CausesIn F.esse) ∧
  -- uniting: nonvacuity, with a composite and a distinct uniter
  (∃ (Composite : Bool → Prop) (ComponentOf : Bool → Bool → Prop)
      (F : UnitingFrame Bool Unit) (Select : UnitingSense → Prop)
      (use : UnitingUse → Bool → Bool → Prop),
    CompositeHasTwoDistinctComponentsReading Composite ComponentOf ∧
    DiverseUnitedOnlyThroughUnitingCauseReading ComponentOf F.Unites ∧
    UnitingCauseCausesBeingReading F.Unites F.CausesIn F.esse ∧
    UnitingCauseSensesExhaustive F Select use ∧ UnitingCauseSenseUnique Select ∧
    UniterCausesInRouteSense F use ∧ NothingCausesItselfInRouteUse use ∧
    CompositeHasAUnitingCauseReading Composite F.CausesIn F.esse ∧ (∃ x, Composite x)) ∧
  -- in act: coverage without exclusivity; the mover is virtually in act, nothing
  -- is formally in act and in potency, and something moves itself
  (∃ (F : ActFrame Unit Unit) (Select : ActSense → Prop) (use : ActUse → Unit → Unit → Prop),
    InActSensesExhaustive F Select use ∧ ¬ InActSenseUnique Select ∧
    MovedOnlyAsInPotencyReading F.MovedIn F.InPotency ∧
    MovesOnlyAsInActReading F.MovesIn (use .moverInAct) ∧
    NotActAndPotencyInSameRespectReading (use .nonSimultaneity) F.InPotency ∧
    ¬ NothingMovesItselfInSameRespectReading F.MovedIn F.MovesIn) ∧
  -- in act: coverage fails, the rest holds
  (∃ (F : ActFrame Unit Unit) (Select : ActSense → Prop) (use : ActUse → Unit → Unit → Prop),
    ¬ InActSensesExhaustive F Select use ∧ InActSenseUnique Select ∧
    MovedOnlyAsInPotencyReading F.MovedIn F.InPotency ∧
    MovesOnlyAsInActReading F.MovesIn (use .moverInAct) ∧
    NotActAndPotencyInSameRespectReading (use .nonSimultaneity) F.InPotency ∧
    ¬ NothingMovesItselfInSameRespectReading F.MovedIn F.MovesIn) ∧
  -- in act: the mixed reading (mover formally-or-virtually, non-simultaneity
  -- formally) does not give the step
  (∃ (F : ActFrame Unit Unit),
    MovedOnlyAsInPotencyReading F.MovedIn F.InPotency ∧
    MovesOnlyAsInActFormallyOrVirtually F ∧ NothingFormallyInActAndInPotency F ∧
    ¬ NothingMovesItselfInSameRespectReading F.MovedIn F.MovesIn) ∧
  -- in act: nonvacuity, with motion
  (∃ (F : ActFrame Bool Unit) (Select : ActSense → Prop) (use : ActUse → Bool → Unit → Prop),
    InActSensesExhaustive F Select use ∧ InActSenseUnique Select ∧
    MovedOnlyAsInPotencyReading F.MovedIn F.InPotency ∧
    MovesOnlyAsInActReading F.MovesIn (use .moverInAct) ∧
    NotActAndPotencyInSameRespectReading (use .nonSimultaneity) F.InPotency ∧
    NothingMovesItselfInSameRespectReading F.MovedIn F.MovesIn ∧
    (∃ y x r, F.MovesIn y x r)) ∧
  -- becoming/being: BECOMING-BEING-CAUSE_1 fails to give the sense-3 root
  -- statement: every participated thing has another cause of its coming to be,
  -- and nothing causes its being
  (∃ (F : BecomingBeingFrame Bool Bool Unit),
    ParticipatedHasOtherCauseOfBecoming F ∧ (∃ x, F.Participated x) ∧
    ¬ TruthCore.Causality.ComponentFirstness.ParticipatedHasOtherCause
      F.Participated F.profile.CausesIn F.profile.esse) ∧
  -- becoming/being: nonvacuity of the sense-2 route
  (∃ (F : BecomingBeingFrame Bool Bool Unit),
    ParticipatedHasDistinctEsse F ∧
    PrimaPars.Question3.Article4.DistinctEsseRequiresExternalCauseReading F.profile ∧
    (∃ x, F.Participated x))

end TruthCore.Causality.TermSenseForks
