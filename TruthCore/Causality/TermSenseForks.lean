module

public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3SecundaVia
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.ActPriorFromIncorruptible
public import TruthCore.Greek.Aristotle.Physics.Typed.Motion

/-! Sense forks for two load-bearing root-path terms: "prior" and "cause"

Analyst formulations, attribution deferred. The disambiguations
DISAMB-PRIORITY-SIMPLE-OR-IN-TIME and DISAMB-CAUSE keep their senses as
separate predicates and say that no step passes between them. This module
relates the senses instead: each term gets an enum of its senses on the route,
a sense-indexed relation that unfolds to the existing Lean parameter of each
sense, a COVERAGE premise (the route's use is read in one of the listed senses)
and an EXCLUSIVITY premise (the route's intended reading selects exactly one
sense). Joint theorems then reach the root-path step by cases over the enum:
each branch either yields the step or is refuted by an explicit open premise
(disjunctive syllogism).

**How exclusivity is formalized.** The senses overlap and may be ordered by
strength, so their extensions are not claimed disjoint. A `Select : Sense →
Prop` is the route's reading choice (which constructor the route intends), not
an extension test; exclusivity (`SenseUnique`) says that at most one
constructor is selected. Together with coverage it gives exactly one. A model
in which two senses have equal extensions is allowed: only the selection is
unique. Strength order between sense-relative propositions is recorded
separately with `strengthens` relations.

**Coverage is attackable.** Coverage lists the senses of the term recorded in
the corpus for this route. A rival who proposes a further sense (for "cause":
grounding, `Ontic.Causes`, or an Aristotelian formal or final cause) denies
coverage; the joint theorems then say nothing about that sense. Coverage and
exclusivity are explicit OPEN frontier premises.

Vocabulary reused exactly, all parameters of the source readings:
`InAct`, `InPotency`, `MovedIn`, `MovesIn` (prima via), `PriorSimply`
(DEF-SIMPLE-PRIORITY), `PriorInSubstance` (DEF-PRIORITY-IN-SUBSTANCE),
`EfficientlyCausesIn` (DEF-EFFICIENT-CAUSING), `CausesIn`
(DEF-CAUSE-OF-PERFECTION) and `CausesOrigin` (DEF-CAUSE-OF-ORIGIN). New:
`PriorInTime` (DEF-PRIORITY-IN-TIME, which had no Lean declaration), a
parameter between beings: `y` is or occurs before `x`. -/

@[expose] public section

namespace TruthCore.Causality.TermSenseForks

open TruthCore.Latin.Aquinas.SummaTheologiae

universe u w

/-! ## Generic sense-fork vocabulary -/

/-- Coverage, generic: every use `u` of the term on the route is read in some
selected sense `σ`, and the use's relation is exactly the relation of that
sense (`interp σ`). -/
def SensesCover {S : Type} {Rel : Sort u} {U : Sort w}
    (interp : S → Rel) (Select : S → Prop) (use : U → Rel) : Prop :=
  ∀ u, ∃ σ, Select σ ∧ use u = interp σ

/-- Exclusivity, generic: the route's reading selects at most one sense.
This is about the reading choice, not about disjoint extensions. -/
def SenseUnique {S : Type} (Select : S → Prop) : Prop :=
  ∀ σ τ, Select σ → Select τ → σ = τ

/-- All uses of the term on the route stand for one relation: no equivocation. -/
def UsesAgree {Rel : Sort u} {U : Sort w} (use : U → Rel) : Prop :=
  ∀ u v, use u = use v

theorem usesAgree_of_cover_unique {S : Type} {Rel : Sort u} {U : Sort w}
    (interp : S → Rel) (Select : S → Prop) (use : U → Rel)
    (hCover : SensesCover interp Select use) (hUnique : SenseUnique Select) :
    UsesAgree use := by
  intro u v
  obtain ⟨σ, hσ, hu⟩ := hCover u
  obtain ⟨τ, hτ, hv⟩ := hCover v
  have hστ : σ = τ := hUnique σ τ hσ hτ
  subst hστ
  exact hu.trans hv.symm

/-! ## "prior" -/

/-- The senses of "prior" on the route to act's priority over potency
(DISAMB-PRIORITY-SIMPLE-OR-IN-TIME): simple priority (ST I q.3 a.1), priority
in time, and priority in substance and perfection (*Met.* Θ.8; *In Metaph.* IX
lect. 9). -/
inductive PrioritySense
  | simply
  | inTime
  | inSubstance
  deriving DecidableEq

/-- The parameters the priority senses are read over. -/
structure PriorityFrame (Being : Type) (Respect : Type) where
  InAct : Being → Respect → Prop
  InPotency : Being → Respect → Prop
  PriorSimply : Being → Being → Prop
  /-- DEF-PRIORITY-IN-TIME: `PriorInTime y x`, `y` is or occurs before `x`. -/
  PriorInTime : Being → Being → Prop
  PriorInSubstance : Being → Being → Prop

/-- The sense-relative priority relation: each constructor unfolds to the
existing parameter of that sense. -/
def PriorityFrame.PriorIn {Being Respect : Type} (F : PriorityFrame Being Respect) :
    PrioritySense → Being → Being → Prop
  | .simply => F.PriorSimply
  | .inTime => F.PriorInTime
  | .inSubstance => F.PriorInSubstance

/-- COVERAGE (STMT-PRIOR-SENSES-EXHAUSTIVE): every use of "prior" on the route
is read in one of simple priority, priority in time or priority in substance,
selected by the route's reading. OPEN frontier premise. -/
def PriorSensesExhaustive {Being Respect : Type} {U : Sort w}
    (F : PriorityFrame Being Respect) (Select : PrioritySense → Prop)
    (use : U → Being → Being → Prop) : Prop :=
  SensesCover F.PriorIn Select use

/-- EXCLUSIVITY (STMT-PRIOR-SENSE-UNIQUE): the route's reading of "prior"
selects at most one sense. Not a disjointness claim. OPEN frontier premise. -/
def PriorSenseUnique (Select : PrioritySense → Prop) : Prop :=
  SenseUnique Select

/-- Every use of "prior" on the route stands for one relation. -/
def PriorRouteUsesAgree {Being : Type} {U : Sort w}
    (use : U → Being → Being → Prop) : Prop :=
  UsesAgree use

/-- Act is prior to potency in the route's sense of "prior" (`RoutePrior`):
whatever is in potency in a respect is posterior, in that sense, to some being
in act in that respect. With `RoutePrior := PriorSimply` this is
`ActSimplyPriorToPotencyReading`. -/
def ActPriorInRouteSense {Being Respect : Type} (F : PriorityFrame Being Respect)
    (RoutePrior : Being → Being → Prop) : Prop :=
  ∀ x r, F.InPotency x r → ∃ y, F.InAct y r ∧ RoutePrior y x

/-- Act is prior to potency in time, over every respect (the temporal branch). -/
def ActPriorInTime {Being Respect : Type} (F : PriorityFrame Being Respect) : Prop :=
  ∀ x r, F.InPotency x r → ∃ y, F.InAct y r ∧ F.PriorInTime y x

/-- Act is prior to potency in substance, over every respect (the substance
branch). Wider than `ActPriorInSubstanceReading`, which is restricted to the
respect `esse`. -/
def ActPriorInSubstance {Being Respect : Type} (F : PriorityFrame Being Respect) : Prop :=
  ∀ x r, F.InPotency x r → ∃ y, F.InAct y r ∧ F.PriorInSubstance y x

/-- The temporal branch fails. -/
def ActNotPriorInTime {Being Respect : Type} (F : PriorityFrame Being Respect) : Prop :=
  ¬ ActPriorInTime F

/-- Some being first in time (nothing is before it) is in potency in some
respect: the cosmogonies of *Met.* XII.6, 1071b26-28 (Night, chaos), and
any world whose first being is changeable. OPEN analyst premise. -/
def TemporallyFirstBeingInPotency {Being Respect : Type}
    (F : PriorityFrame Being Respect) : Prop :=
  ∃ n r, (∀ y, ¬ F.PriorInTime y n) ∧ F.InPotency n r

/-! ## "cause" -/

/-- The senses of "cause" recorded for the root path in DISAMB-CAUSE: moving
(`MovesIn`, reduction from potency to act), efficient causing
(`EfficientlyCausesIn`, secunda via), causing a perfection (`CausesIn`, with
cause of being at esse), and cause of origin (`CausesOrigin`, SCG I.13). -/
inductive CauseSense
  | moving
  | efficient
  | perfection
  | origin
  deriving DecidableEq

/-- The parameters the causal senses are read over. -/
structure CauseFrame (Being : Type) (Respect : Type) where
  MovedIn : Being → Respect → Prop
  MovesIn : Being → Being → Respect → Prop
  EfficientlyCausesIn : Being → Being → Respect → Prop
  CausesIn : Being → Being → Respect → Prop
  CausesOrigin : Being → Being → Prop

/-- The sense-relative causal relation `c` causes `x` in respect `r`; each
constructor unfolds to the existing parameter of that sense. Origin has no
respect, so it ignores `r`. -/
def CauseFrame.CausesBy {Being Respect : Type} (F : CauseFrame Being Respect) :
    CauseSense → Being → Being → Respect → Prop
  | .moving => F.MovesIn
  | .efficient => F.EfficientlyCausesIn
  | .perfection => F.CausesIn
  | .origin => fun c x _ => F.CausesOrigin c x

/-- COVERAGE (STMT-CAUSE-SENSES-EXHAUSTIVE): every use of "cause" on the route
is read in one of moving, efficient causing, causing a perfection, or cause of
origin, selected by the route's reading. OPEN frontier premise. -/
def CauseSensesExhaustive {Being Respect : Type} {U : Sort w}
    (F : CauseFrame Being Respect) (Select : CauseSense → Prop)
    (use : U → Being → Being → Respect → Prop) : Prop :=
  SensesCover F.CausesBy Select use

/-- EXCLUSIVITY (STMT-CAUSE-SENSE-UNIQUE): the route's reading of "cause"
selects at most one sense. Not a disjointness claim. OPEN frontier premise. -/
def CauseSenseUnique (Select : CauseSense → Prop) : Prop :=
  SenseUnique Select

/-- Every use of "cause" on the route stands for one relation. -/
def CauseRouteUsesAgree {Being Respect : Type} {U : Sort w}
    (use : U → Being → Being → Respect → Prop) : Prop :=
  UsesAgree use

/-- Nothing causes itself in any respect, "cause" in the route's sense. -/
def NothingCausesItselfInRouteSense {Being Respect : Type}
    (RouteCause : Being → Being → Respect → Prop) : Prop :=
  ∀ x r, ¬ RouteCause x x r

/-- Nothing causes a perfection in itself (the perfection branch). -/
def NothingCausesItsOwnPerfection {Being Respect : Type}
    (F : CauseFrame Being Respect) : Prop :=
  ∀ x r, ¬ F.CausesIn x x r

/-- Some subject causes a perfection in itself, as a subject causes its proper
accidents from its own principles. OPEN analyst premise. -/
def SomeSubjectCausesItsOwnPerfection {Being Respect : Type}
    (F : CauseFrame Being Respect) : Prop :=
  ∃ x r, F.CausesIn x x r

/-- The perfection branch fails: not everything's perfections are caused by
something other than it. -/
def OwnPerfectionNotAlwaysExternal {Being Respect : Type}
    (F : CauseFrame Being Respect) : Prop :=
  ¬ NothingCausesItsOwnPerfection F

/-- A thing that efficiently caused itself in some respect would move itself in
that respect. OPEN analyst bridge (efficient causing as source of motion). -/
def SelfEfficientCausationIsSelfMoving {Being Respect : Type}
    (F : CauseFrame Being Respect) : Prop :=
  ∀ x r, F.EfficientlyCausesIn x x r → F.MovesIn x x r

/-- Nothing is the originating cause of itself. -/
def NothingOriginatesItself {Being Respect : Type} (F : CauseFrame Being Respect) : Prop :=
  ∀ x, ¬ F.CausesOrigin x x

/-- A thing that efficiently caused itself in some respect would be a cause of
its own coming to be. OPEN analyst bridge. -/
def SelfEfficientCausationIsSelfOrigination {Being Respect : Type}
    (F : CauseFrame Being Respect) : Prop :=
  ∀ x r, F.EfficientlyCausesIn x x r → F.CausesOrigin x x

end TruthCore.Causality.TermSenseForks

namespace TruthCore.Causality.TermSenseForks

open TruthCore.Latin.Aquinas.SummaTheologiae

/-! ## Controls

Finite interpretations over one- or two-element carriers. Each omission row
gives a model in which every premise of the named theorem except one holds and
its conclusion fails; each witness row gives a model in which every premise and
the conclusion hold with the route relation nonempty. Satisfiability and
omission only; no model describes reality. -/

/-- Controls of the "prior" fork. -/
def PriorForkControls : Prop :=
  -- omission of coverage
  (∃ (F : PriorityFrame Unit Unit) (Select : PrioritySense → Prop) (RP : Unit → Unit → Prop),
    ¬ PriorSensesExhaustive F Select (fun _ : Unit => RP) ∧ ActPriorInRouteSense F RP ∧
    PriorInSubstanceIsSimpleReading F.PriorInSubstance F.PriorSimply ∧
    TemporallyFirstBeingInPotency F ∧
    ¬ ActSimplyPriorToPotencyReading F.InAct F.InPotency F.PriorSimply) ∧
  -- omission of the route premise
  (∃ (F : PriorityFrame Unit Unit) (Select : PrioritySense → Prop) (RP : Unit → Unit → Prop),
    PriorSensesExhaustive F Select (fun _ : Unit => RP) ∧ ¬ ActPriorInRouteSense F RP ∧
    PriorInSubstanceIsSimpleReading F.PriorInSubstance F.PriorSimply ∧
    TemporallyFirstBeingInPotency F ∧
    ¬ ActSimplyPriorToPotencyReading F.InAct F.InPotency F.PriorSimply) ∧
  -- omission of the substance bridge (the substance branch survives)
  (∃ (F : PriorityFrame Unit Unit) (Select : PrioritySense → Prop) (RP : Unit → Unit → Prop),
    PriorSensesExhaustive F Select (fun _ : Unit => RP) ∧ ActPriorInRouteSense F RP ∧
    ¬ PriorInSubstanceIsSimpleReading F.PriorInSubstance F.PriorSimply ∧
    TemporallyFirstBeingInPotency F ∧
    ¬ ActSimplyPriorToPotencyReading F.InAct F.InPotency F.PriorSimply) ∧
  -- omission of the temporally-first potency (the temporal branch survives)
  (∃ (F : PriorityFrame Unit Unit) (Select : PrioritySense → Prop) (RP : Unit → Unit → Prop),
    PriorSensesExhaustive F Select (fun _ : Unit => RP) ∧ ActPriorInRouteSense F RP ∧
    PriorInSubstanceIsSimpleReading F.PriorInSubstance F.PriorSimply ∧
    ¬ TemporallyFirstBeingInPotency F ∧
    ¬ ActSimplyPriorToPotencyReading F.InAct F.InPotency F.PriorSimply) ∧
  -- nonvacuity: every premise and the conclusion, with a potency and a prior being
  (∃ (F : PriorityFrame Unit Unit) (Select : PrioritySense → Prop) (RP : Unit → Unit → Prop),
    PriorSensesExhaustive F Select (fun _ : Unit => RP) ∧ PriorSenseUnique Select ∧
    ActPriorInRouteSense F RP ∧
    PriorInSubstanceIsSimpleReading F.PriorInSubstance F.PriorSimply ∧
    TemporallyFirstBeingInPotency F ∧
    ActSimplyPriorToPotencyReading F.InAct F.InPotency F.PriorSimply ∧
    (∃ x r, F.InPotency x r) ∧ (∃ y x, RP y x)) ∧
  -- exclusivity carries uses-agree: two selected senses, two different relations
  (∃ (F : PriorityFrame Unit Unit) (Select : PrioritySense → Prop)
      (use : Bool → Unit → Unit → Prop),
    PriorSensesExhaustive F Select use ∧ ¬ PriorSenseUnique Select ∧
    ¬ PriorRouteUsesAgree use)

/-- Controls of the "cause" fork. -/
def CauseForkControls : Prop :=
  -- omission of coverage
  (∃ (F : CauseFrame Unit Unit) (Select : CauseSense → Prop) (RC : Unit → Unit → Unit → Prop),
    ¬ CauseSensesExhaustive F Select (fun _ : Unit => RC) ∧
    NothingCausesItselfInRouteSense RC ∧ SomeSubjectCausesItsOwnPerfection F ∧
    SelfEfficientCausationIsSelfMoving F ∧ SelfEfficientCausationIsSelfOrigination F ∧
    ¬ NothingIsEfficientCauseOfItselfReading F.EfficientlyCausesIn) ∧
  -- omission of the route premise
  (∃ (F : CauseFrame Unit Unit) (Select : CauseSense → Prop) (RC : Unit → Unit → Unit → Prop),
    CauseSensesExhaustive F Select (fun _ : Unit => RC) ∧
    ¬ NothingCausesItselfInRouteSense RC ∧ SomeSubjectCausesItsOwnPerfection F ∧
    SelfEfficientCausationIsSelfMoving F ∧ SelfEfficientCausationIsSelfOrigination F ∧
    ¬ NothingIsEfficientCauseOfItselfReading F.EfficientlyCausesIn) ∧
  -- omission of the self-perfecting subject (the perfection branch survives)
  (∃ (F : CauseFrame Unit Unit) (Select : CauseSense → Prop) (RC : Unit → Unit → Unit → Prop),
    CauseSensesExhaustive F Select (fun _ : Unit => RC) ∧
    NothingCausesItselfInRouteSense RC ∧ ¬ SomeSubjectCausesItsOwnPerfection F ∧
    SelfEfficientCausationIsSelfMoving F ∧ SelfEfficientCausationIsSelfOrigination F ∧
    ¬ NothingIsEfficientCauseOfItselfReading F.EfficientlyCausesIn) ∧
  -- omission of the moving bridge (the moving branch survives)
  (∃ (F : CauseFrame Unit Unit) (Select : CauseSense → Prop) (RC : Unit → Unit → Unit → Prop),
    CauseSensesExhaustive F Select (fun _ : Unit => RC) ∧
    NothingCausesItselfInRouteSense RC ∧ SomeSubjectCausesItsOwnPerfection F ∧
    ¬ SelfEfficientCausationIsSelfMoving F ∧ SelfEfficientCausationIsSelfOrigination F ∧
    ¬ NothingIsEfficientCauseOfItselfReading F.EfficientlyCausesIn) ∧
  -- omission of the origin bridge (the origin branch survives)
  (∃ (F : CauseFrame Unit Unit) (Select : CauseSense → Prop) (RC : Unit → Unit → Unit → Prop),
    CauseSensesExhaustive F Select (fun _ : Unit => RC) ∧
    NothingCausesItselfInRouteSense RC ∧ SomeSubjectCausesItsOwnPerfection F ∧
    SelfEfficientCausationIsSelfMoving F ∧ ¬ SelfEfficientCausationIsSelfOrigination F ∧
    ¬ NothingIsEfficientCauseOfItselfReading F.EfficientlyCausesIn) ∧
  -- nonvacuity: every premise and the conclusion, with efficient causing nonempty
  (∃ (F : CauseFrame Bool Unit) (Select : CauseSense → Prop) (RC : Bool → Bool → Unit → Prop),
    CauseSensesExhaustive F Select (fun _ : Unit => RC) ∧ CauseSenseUnique Select ∧
    NothingCausesItselfInRouteSense RC ∧ SomeSubjectCausesItsOwnPerfection F ∧
    SelfEfficientCausationIsSelfMoving F ∧ SelfEfficientCausationIsSelfOrigination F ∧
    NothingIsEfficientCauseOfItselfReading F.EfficientlyCausesIn ∧
    (∃ c x r, F.EfficientlyCausesIn c x r)) ∧
  -- exclusivity carries uses-agree
  (∃ (F : CauseFrame Unit Unit) (Select : CauseSense → Prop)
      (use : Bool → Unit → Unit → Unit → Prop),
    CauseSensesExhaustive F Select use ∧ ¬ CauseSenseUnique Select ∧
    ¬ CauseRouteUsesAgree use)

/-- The controls of the batch: both forks. -/
def TermSenseForkControls : Prop :=
  PriorForkControls ∧ CauseForkControls

end TruthCore.Causality.TermSenseForks
