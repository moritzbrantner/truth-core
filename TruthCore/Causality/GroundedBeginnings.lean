module

public import TruthCore.Causality.InertEmptiness
public import TruthCore.Causality.BegunComingToBe

/-!
# Grounded beginnings: a causal route to inert emptiness

Analyst formulation for the modal spine to "God exists"
(`docs/notes/modal-spine.md`, premise A2 of Arrival A). Attribution deferred;
no source is claimed.

Premise A2, `InertEmptiness.EmptinessStaysEmpty`, says that a moment with
nothing concrete present is followed only by such moments. It is stated without
any cause or ground. This module derives it, through a precise traced form of
"from nothing, nothing comes", from two principles about a supplied
world-relative grounding relation `grounds v y x` ("in history `v`, `y` is a
ground of `x`", the same shape as `BruteFoundationBoundary.Profile.grounds`).

**Sense of "ground".** The relation is a supplied parameter. The intended
reading for the warrant is the *proximate ground of a thing's coming to be*
(the cause from which its coming to be takes its origin), not a remote ancestor.
The derivation is valid for any relation. Both principles cover per se and
per accidens grounds alike (`DISAMB-CAUSAL-SERIES`). *Concrete* is the
supplied `Concrete` predicate, as in A2 (`DISAMB-CONCRETE-ABSTRACT-CRITERIA`).

**Ordinary meaning.**

* *Beginnings have a lasting ground* (`BeginningsHaveLastingGround`, A2ab): a
  concrete thing that is absent at a moment `s` and present at a strictly later
  moment of the same history has *some* concrete ground that is present at `s`
  or at some moment after `s`. In other words, whatever begins to be present has
  a concrete ground that had not wholly ceased before the beginning's interval.
  A fire lit at noon, absent at dawn, whose match is present just before
  ignition, satisfies it. It is existential, so a remote ground that ceased
  long ago (a grandparent who died before `s`, of a child born after `s`) does
  not violate it, as long as some ground (a parent) is present at `s` or later.
  A thing present from the earliest moment of its history, or never present, is
  unconstrained.
* *Grounding is well-founded after an absence* (`PostAbsenceGroundingWellFounded`,
  A2c): for every history and moment `s`, among concrete things that are absent
  at `s` and present at some later moment, there is no endless descending chain
  of grounds. An endless series of grounds reaching into an endless past (each
  thing grounded by an earlier one, none ever absent before its predecessor's
  time) is *not* excluded: its members are not all absent at any one moment
  (`Control.beginningless`). What is excluded is an endless series of grounds
  compressed into the stretch after one moment at which all its members are
  absent.

**Traced form of "from nothing, nothing comes"** (`NothingFromNothing`): a
concrete thing present at a moment `t` traces back, through a finite chain of
grounding links (possibly of length zero), to a concrete thing present at any
given earlier moment `s`. It strictly strengthens A2: A2 is the special case
that something concrete is present at `s`.

**Distinctions.** Neither principle is a principle of sufficient reason:
grounds are required only for beginnings, only concrete grounds count, and
nothing is said about explanation of facts. A2ab is not
`BruteFoundationBoundary.EveryContingentGroundedAt`: it concerns every concrete
thing that comes to be present (contingent or not) and no thing that never
comes to be present. Its presence clause bounds the ground's presence from
*below* (not wholly before the absence), whereas
`ComingToBeHorns.GroundsPrecedeAt` bounds it from *above* (before the
presence); the latter holds in `BegunComingToBe.Control.zeno` and does not give
A2. A2c is strictly weaker than well-foundedness of grounding among all concrete
things present in a history (`PresentGroundingWellFounded`), which an endless
past of fathers violates.

**Structural properties.** The grounding relation is not assumed transitive,
asymmetric or irreflexive. No linear order, first moment, discreteness or
density of time is assumed. The principles quantify over every history of the
model, like A2.

**Bridges and rivals.** Extending "ordinary beginnings have concrete grounds
that do not act across an empty gap" to every possible history, including one
whose earlier moment is wholly empty, is an explicit OPEN bridge. The checked
controls show each principle is needed for A2 in one interpretation: a
ground-free beginning out of nothing; a beginning whose only ground ceased
before an empty moment; and an endless chain of present concrete grounds
descending towards an empty first moment (`BegunComingToBe.Control.zeno`, times
`WithBot ℤ`). That last shape is the strongest formal rival compatible with
A2ab. Its endless chain may descend in time towards the empty moment, as in
`zeno`, or (not checked here) be an endless regress of grounds all present at
one later moment.

**No modal content.** The two principles and the traced form hold in
`InertEmptiness.Control.initialState` with no grounding at all, where no
concrete individual is necessary at any world. So, unlike the founded-past
grounding bundle (`ComingToBeHorns.possiblyNecessaryOfEarlierGrounds`), they
do not contain the possibility of a necessary concrete being. In Arrival A,
necessity arises from A2 jointly with A3, presence-to-existence and the frame
premises; none of them suffices without A2 (`InertEmptiness.Control.exNihilo`).

Applicability of every definition below to reality remains OPEN.
-/

@[expose] public section

namespace TruthCore.Causality.GroundedBeginnings

open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Modal.TemporalHistory
open TruthCore.Causality.InertEmptiness

/-- `x` is concrete and present at some moment of history `v`. -/
def ConcretelyPresentIn {W B T : Type} (h : History W B T) (Concrete : B → Prop)
    (v : W) (x : B) : Prop :=
  Concrete x ∧ ∃ u, h.IsAt v x u

/-- `x` is concrete, absent at `s` and present at some moment strictly after
`s`, in history `v`. -/
def ComesToBeAfter {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) (v : W) (s : T) (x : B) : Prop :=
  Concrete x ∧ ¬ h.IsAt v x s ∧ ∃ u, s < u ∧ h.IsAt v x u

/-- In every history, a concrete thing absent at a moment and present at a
strictly later moment has a concrete ground under the supplied relation. Used
only in the controls: without a presence condition on the ground it does not
give inert emptiness. -/
def BeginningsGrounded {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) (grounds : W → B → B → Prop) : Prop :=
  ∀ v x s t, Concrete x → s < t → ¬ h.IsAt v x s → h.IsAt v x t →
    ∃ y, Concrete y ∧ grounds v y x

/-- In every history, a concrete thing absent at `s` and present at a strictly
later `t` has some concrete ground that is present at `s` or at some moment
strictly after `s`. The ground may be simultaneous with the thing, or later;
other grounds of the thing are unconstrained. -/
def BeginningsHaveLastingGround {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) (grounds : W → B → B → Prop) : Prop :=
  ∀ v x s t, Concrete x → s < t → ¬ h.IsAt v x s → h.IsAt v x t →
    ∃ y, Concrete y ∧ grounds v y x ∧ (h.IsAt v y s ∨ ∃ u, s < u ∧ h.IsAt v y u)

/-- In every history and for every moment `s`, grounding among concrete things
that are absent at `s` and present at some later moment is well-founded. -/
def PostAbsenceGroundingWellFounded {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) (grounds : W → B → B → Prop) : Prop :=
  ∀ v s, WellFounded fun y x =>
    ComesToBeAfter h Concrete v s y ∧ ComesToBeAfter h Concrete v s x ∧ grounds v y x

/-- In every history, grounding restricted to concrete things present at some
moment of that history is well-founded. Strictly stronger than
`PostAbsenceGroundingWellFounded`. -/
def PresentGroundingWellFounded {W B T : Type} (h : History W B T)
    (Concrete : B → Prop) (grounds : W → B → B → Prop) : Prop :=
  ∀ v, WellFounded fun y x =>
    ConcretelyPresentIn h Concrete v y ∧ ConcretelyPresentIn h Concrete v x ∧ grounds v y x

/-- Traced "from nothing, nothing comes": in every history, a concrete thing
present at `t` has, for every strictly earlier `s`, a concrete thing present at
`s` from which it descends by a finite chain of grounding links, possibly of
length zero (the thing itself). -/
def NothingFromNothing {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) (grounds : W → B → B → Prop) : Prop :=
  ∀ v x s t, Concrete x → s < t → h.IsAt v x t →
    ∃ y, Concrete y ∧ h.IsAt v y s ∧ Relation.ReflTransGen (grounds v) y x

namespace Control

open TruthCore.Causality.InertEmptiness.Control (universal all exNihilo initialState rooted)
open TruthCore.Causality.BegunComingToBe.Control (zeno predecessorGrounds)

/-- No grounding at all. -/
def noGrounds {W B : Type} : W → B → B → Prop := fun _ _ _ => False

/-- Individual `false` grounds individual `true`, at every world. -/
def falseGroundsTrue : Bool → Bool → Bool → Prop := fun _ y x => y = false ∧ x = true

/-- A ground that ceased before an empty moment. At world `true`, individual
`false` is present only at time 0 and individual `true` only at time 2; time 1
is empty. Nothing exists at world `false`. -/
def ceased : History Bool Bool Nat where
  ontic := { frame := universal, ExistsAt := fun w _ => w = true, Causes := fun _ _ _ => False }
  IsAt := fun w x t => w = true ∧ ((x = false ∧ t = 0) ∨ (x = true ∧ t = 2))
  now := 2

/-- An endless past of grounds with no empty moment. Worlds are booleans,
individuals and times integers. At world `true` individual `n` exists and is
present at every time `t ≥ n`, and (with `predecessorGrounds`) is grounded by
`n - 1`. Nothing exists at world `false`. -/
def beginningless : History Bool Int Int where
  ontic := { frame := universal, ExistsAt := fun w _ => w = true, Causes := fun _ _ _ => False }
  IsAt := fun w n t => w = true ∧ n ≤ t
  now := 0

/-- Omission, strictness, no-modal-content and nonvacuity controls, every
individual counted concrete. (1) `exNihilo` without grounds: post-absence
well-foundedness holds; lasting grounds and inert emptiness fail. (2) `ceased`
with `false` grounding `true`: every beginning has a concrete ground and
post-absence well-foundedness holds; lasting grounds and inert emptiness fail.
(3) `zeno` with predecessor grounds: lasting grounds hold; post-absence
well-foundedness and inert emptiness fail. (4) `initialState` without grounds:
both principles and the traced form hold, and no concrete individual is
necessary at either world. (5) `rooted` without grounds: inert emptiness holds
and the traced form fails. (6) `rooted` with `false` grounding `true`: both
principles, presence-to-existence and the possible contingent-free past hold,
and a concrete individual is necessary at world `true`. (7) `beginningless`
with predecessor grounds: both principles and inert emptiness hold, while
well-foundedness of grounding among all present concrete things fails. -/
def Certificate : Prop :=
  (PostAbsenceGroundingWellFounded exNihilo all noGrounds ∧
    ¬ BeginningsHaveLastingGround exNihilo all noGrounds ∧
    ¬ EmptinessStaysEmpty exNihilo all) ∧
  (BeginningsGrounded ceased all falseGroundsTrue ∧
    PostAbsenceGroundingWellFounded ceased all falseGroundsTrue ∧
    ¬ BeginningsHaveLastingGround ceased all falseGroundsTrue ∧
    ¬ EmptinessStaysEmpty ceased all) ∧
  (BeginningsHaveLastingGround zeno all predecessorGrounds ∧
    ¬ PostAbsenceGroundingWellFounded zeno all predecessorGrounds ∧
    ¬ EmptinessStaysEmpty zeno all) ∧
  (BeginningsHaveLastingGround initialState all noGrounds ∧
    PostAbsenceGroundingWellFounded initialState all noGrounds ∧
    NothingFromNothing initialState all noGrounds ∧
    ∀ v, ¬ BruteFoundationBoundary.NecessaryConcreteAt
      ⟨initialState.ontic, all, noGrounds⟩ v) ∧
  (EmptinessStaysEmpty rooted all ∧ ¬ NothingFromNothing rooted all noGrounds) ∧
  (BeginningsHaveLastingGround rooted all falseGroundsTrue ∧
    PostAbsenceGroundingWellFounded rooted all falseGroundsTrue ∧
    CountTemporalNecessity.HistoryPresenceActual rooted ∧
    PossiblyContingentsAbsentThenPresent rooted all true ∧
    BruteFoundationBoundary.NecessaryConcreteAt ⟨rooted.ontic, all, falseGroundsTrue⟩ true) ∧
  (BeginningsHaveLastingGround beginningless all predecessorGrounds ∧
    PostAbsenceGroundingWellFounded beginningless all predecessorGrounds ∧
    EmptinessStaysEmpty beginningless all ∧
    ¬ PresentGroundingWellFounded beginningless all predecessorGrounds)

end Control

end TruthCore.Causality.GroundedBeginnings
