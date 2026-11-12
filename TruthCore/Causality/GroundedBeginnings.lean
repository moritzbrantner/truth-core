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
"from nothing, nothing comes", from three principles about a supplied
world-relative grounding relation `grounds v y x` ("in history `v`, `y` is a
ground of `x`", the same shape as `BruteFoundationBoundary.Profile.grounds`).

**Ordinary meaning.**

* *Beginnings are concretely grounded* (`BeginningsGrounded`): a concrete thing
  that is absent at a moment and present at a later moment of the same history
  has a concrete ground. This is "whatever begins to be present has a concrete
  cause or ground", with *begins* read as "absent at some earlier moment". It is
  silent about a thing present from the earliest moment of a history, and about
  things never present at any moment.
* *Grounds have not ceased before the absence* (`GroundsNotCeasedBeforeAbsence`):
  a ground of such a thing is present at the moment of its absence or at some
  later moment. It forbids exactly a ground that existed only before that moment
  and then produced the thing across the gap. Ordinary causes satisfy it: the
  match that lights the fire is present just before ignition. It does not
  require the ground to precede the thing (it may be simultaneous or even later),
  and it is weaker than temporal locality ("present at some moment from the
  absence up to the presence").
* *Grounding among present concrete things is well-founded*
  (`PresentGroundingWellFounded`): in each history, among concrete things present
  at some moment, there is no endless descending chain of grounds.

**Traced form of "from nothing, nothing comes"** (`NothingFromNothing`): a
concrete thing present at a moment `t` traces back, through a finite chain of
grounding links (possibly of length zero), to a concrete thing present at any
given earlier moment `s`. It strictly strengthens A2: A2 is the special case
that something concrete is present at `s`.

**Distinctions.** None of these is a principle of sufficient reason: grounds
are required only for beginnings, only concrete grounds count, and nothing is
said about explanation of facts. `BeginningsGrounded` is not
`BruteFoundationBoundary.EveryContingentGroundedAt`: it concerns every concrete
thing that comes to be present (contingent or not) and no thing that never
comes to be present (contingent or not). `GroundsNotCeasedBeforeAbsence` bounds
the ground's presence from *below* (not entirely before the absence), whereas
`ComingToBeHorns.GroundsPrecedeAt` bounds it from *above* (before the presence);
the latter is satisfied by the endless descent of `BegunComingToBe.Control.zeno`
and does not give A2.

**Structural properties.** The grounding relation is not assumed transitive,
asymmetric or irreflexive; well-foundedness is assumed only among concrete
things present at some moment of the same history. No linear order, first
moment, discreteness or density of time is assumed. The principles quantify
over every history of the model, like A2.

**Bridges and rivals.** Extending "ordinary beginnings have concrete causes
that do not act across an empty gap" to every possible history, including one
whose earlier moment is wholly empty, is an explicit OPEN bridge. The checked
controls show each of the three principles is needed for A2 in one
interpretation: a beginning with no ground; a ground that ceased before an
empty moment; and an endless chain of grounds descending towards an empty first
moment (`BegunComingToBe.Control.zeno`, times `WithBot ℤ`). That last shape is
the strongest formal rival compatible with the first two principles: everything
that begins has a present concrete ground, yet a populated stretch follows an
empty moment. It needs an empty moment that is a moment of the history
followed by moments with no earliest one.

**No re-import of the conclusion.** The three principles and the traced form
hold in `InertEmptiness.Control.initialState` with no grounding at all, where
no concrete individual is necessary at any world. So, unlike the founded-past
grounding bundle (`ComingToBeHorns.possiblyNecessaryOfEarlierGrounds`), they
do not contain the possibility of a necessary concrete being; in Arrival A,
necessity still comes from A3, presence-to-existence and the frame premises.

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

/-- In every history, a concrete thing absent at a moment and present at a
strictly later moment has a concrete ground in that history. Nothing is said
of things present from the earliest moment, or never present. -/
def BeginningsGrounded {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) (grounds : W → B → B → Prop) : Prop :=
  ∀ v x s t, Concrete x → s < t → ¬ h.IsAt v x s → h.IsAt v x t →
    ∃ y, Concrete y ∧ grounds v y x

/-- In every history, if a concrete thing is absent at `s` and present at a
strictly later `t`, each of its grounds is present at `s` or at some moment
strictly after `s`: no ground has wholly ceased before the absence. The ground
may be simultaneous with the thing, or later. -/
def GroundsNotCeasedBeforeAbsence {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) (grounds : W → B → B → Prop) : Prop :=
  ∀ v x y s t, Concrete x → s < t → ¬ h.IsAt v x s → h.IsAt v x t →
    grounds v y x → h.IsAt v y s ∨ ∃ u, s < u ∧ h.IsAt v y u

/-- In every history, grounding restricted to concrete things present at some
moment of that history is well-founded: no endless descending chain of grounds
among them. -/
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

/-- Omission, strictness, no-re-import and nonvacuity controls, every individual
counted concrete. (1) `exNihilo` without grounds: grounds-not-ceased and
well-foundedness hold, beginnings-grounded and inert emptiness fail. (2)
`ceased` with `false` grounding `true`: beginnings-grounded and well-foundedness
hold, grounds-not-ceased and inert emptiness fail. (3) `zeno` with predecessor
grounds: beginnings-grounded and grounds-not-ceased hold, well-foundedness and
inert emptiness fail. (4) `initialState` without grounds: all three principles
and the traced form hold, and no concrete individual is necessary at either
world. (5) `rooted` without grounds: inert emptiness holds and the traced form
fails. (6) `rooted` with `false` grounding `true`: the three principles,
presence-to-existence and the possible contingent-free past hold, and a
concrete individual is necessary at world `true`. -/
def Certificate : Prop :=
  (GroundsNotCeasedBeforeAbsence exNihilo all noGrounds ∧
    PresentGroundingWellFounded exNihilo all noGrounds ∧
    ¬ BeginningsGrounded exNihilo all noGrounds ∧
    ¬ EmptinessStaysEmpty exNihilo all) ∧
  (BeginningsGrounded ceased all falseGroundsTrue ∧
    PresentGroundingWellFounded ceased all falseGroundsTrue ∧
    ¬ GroundsNotCeasedBeforeAbsence ceased all falseGroundsTrue ∧
    ¬ EmptinessStaysEmpty ceased all) ∧
  (BeginningsGrounded zeno all predecessorGrounds ∧
    GroundsNotCeasedBeforeAbsence zeno all predecessorGrounds ∧
    ¬ PresentGroundingWellFounded zeno all predecessorGrounds ∧
    ¬ EmptinessStaysEmpty zeno all) ∧
  (BeginningsGrounded initialState all noGrounds ∧
    GroundsNotCeasedBeforeAbsence initialState all noGrounds ∧
    PresentGroundingWellFounded initialState all noGrounds ∧
    NothingFromNothing initialState all noGrounds ∧
    ∀ v, ¬ BruteFoundationBoundary.NecessaryConcreteAt
      ⟨initialState.ontic, all, noGrounds⟩ v) ∧
  (EmptinessStaysEmpty rooted all ∧ ¬ NothingFromNothing rooted all noGrounds) ∧
  (BeginningsGrounded rooted all falseGroundsTrue ∧
    GroundsNotCeasedBeforeAbsence rooted all falseGroundsTrue ∧
    PresentGroundingWellFounded rooted all falseGroundsTrue ∧
    CountTemporalNecessity.HistoryPresenceActual rooted ∧
    PossiblyContingentsAbsentThenPresent rooted all true ∧
    BruteFoundationBoundary.NecessaryConcreteAt ⟨rooted.ontic, all, falseGroundsTrue⟩ true)

end Control

end TruthCore.Causality.GroundedBeginnings
