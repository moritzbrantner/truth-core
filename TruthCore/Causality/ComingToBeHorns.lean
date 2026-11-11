module

public import TruthCore.Causality.ContingentComingToBe
public import TruthCore.Causality.IndexedSignalReaper
public import TruthCore.Case.Catholicism.StageOne.CausalFinitism
public import Mathlib.Algebra.Order.Field.Rat

/-!
# Pricing the two horns left to the initial-state view

Analyst formulation for the modal spine to "God exists"
(`docs/notes/modal-spine.md`, premise A3′). Attribution deferred.

`ContingentComingToBe.possibleContingentFreePast` derives premise A3 from the
possibility of founded coming-to-be. A holder of the initial-state view who
denies that possibility must say of every accessible history either
(H1) some contingent concrete thing was never preceded by its own absence, or
(H2) no moment at which a contingent concrete thing is present has a founded
past. This module states the bridges under which existing results put a price
on each horn.

**H2 (non-well-founded populated past).** "Founded" is `Acc` of the strict
order of moments. H2 therefore covers an endless past *and* a dense past with a
first moment: on non-negative rational times, every moment after 0 has the
endless descent `t, t/2, t/4, …` below it (`Control.densePast`). Denying H2
everywhere (`PopulatedPastsFounded`) thus forbids a contingent concrete thing
to be present at any non-initial moment of a dense-time history. That is an
anti-continuum price paid by this side, not by the rival. Two formulations:

* `StateCausalFinitism` with `PrecedenceIsStateCausation`: momentary total
  states of each accessible history, related by a state-causation relation on
  moments, have finitely many causal ancestors (modal, event-based causal
  finitism, reusing `FiniteDistinctAncestry`), and every earlier moment's state
  is a causal ancestor of the state at a populated moment. The second premise
  is the explicit bridge from mere temporal precedence to causation; a past of
  mere succession with causally idle earlier states rejects it. This is the one
  derivation with independent content.
* `ReaperAssembly`: along any strictly descending sequence of moments below a
  populated moment of an accessible history, a Nat-indexed Reaper station
  system obeying the four local rules of `IndexedSignalReaper` exists. Its
  consequent is a closed proposition about `Nat` functions that never mentions
  the sequence, the history or its moments, and the verified
  `IndexedSignalReaper.impossible` refutes it. So the bridge is equivalent to
  "no such descent exists": a reformulation of `PopulatedPastsFounded`, and
  its result is recorded as a near-transcription. A genuine patchwork premise
  would need a vocabulary for assembling worlds from local pieces, which the
  corpus lacks. A finite-to-global form over `Nat` functions is already
  refuted as mathematics (`GrimReaperFiniteTests`).

**H1 (a never-generated contingent thing).** `GroundsPrecedeAt` says that every
ground of a contingent concrete thing is present at some moment strictly
before each moment at which the grounded thing is present. A sustaining ground
present at all times satisfies it only if the grounded thing is never present
at a moment with nothing earlier (control 4). It fails exactly when some ground has no
moment of presence before some moment of the grounded thing, in particular at
a moment with nothing earlier. With a founded past it makes an H1 thing
ungrounded, against `BruteFoundationBoundary.EveryContingentGroundedAt`.
Rejecting it does not by itself mean simultaneous grounding: the grounding
relation carries no temporal-presence constraint, so a ground may be
simultaneous, later, or never present (`Control.laterGround`).

**What the H1 bundle already contains.** `PopulatedPastsFounded` together with
`PossiblyEarlierGroundedPopulated` entails that possibly a necessary concrete
individual exists (`PossiblyNecessaryConcrete`): in the witnessing history the
earlier grounds descend along a founded past and must stop at a non-contingent
concrete ground. A rival who denies that a necessary concrete being is so much
as possible therefore rejects that bundle outright.

The grounding relation is a supplied world-relative relation as in
`BruteFoundationBoundary.Profile`; the state-causation relation is a separate
supplied relation on moments. Neither is identified with the other or with the
`Causes` field of the history's ontology. Applicability of every definition
below to reality remains OPEN.
-/

@[expose] public section

namespace TruthCore.Causality.ComingToBeHorns

open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Modal.TemporalHistory
open TruthCore.Causality.InertEmptiness
open TruthCore.Causality.ContingentComingToBe
open TruthCore.Causality.IndexedSignalProvenance
open TruthCore.Causality.IndexedSignalReaper
open TruthCore.Case.Catholicism.StageOne.CausalFinitism

/-- In every history accessible from `w`, every moment at which some
contingent concrete individual is present has a founded past (no endless
descending sequence of moments below it). This denies horn H2 for every
accessible history in which a contingent concrete thing is present at all. -/
def PopulatedPastsFounded {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) (w : W) : Prop :=
  ∀ v, h.ontic.frame.access w v → ∀ x t, Concrete x → ContingentAt h.ontic v x →
    h.IsAt v x t → Acc (fun a b : T => a < b) t

/-- Reaper assembly bridge: for every history accessible from `w` and every
endless strictly descending sequence of moments starting at a moment where a
contingent concrete individual is present, some Nat-indexed system of Reaper
stations satisfies index admissibility, positive trigger, emission and
forwarding (the four local rules of `IndexedSignalReaper`). Station `n` is
read as sitting at the `n`-th moment of the sequence. -/
def ReaperAssembly {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) (w : W) : Prop :=
  ∀ v, h.ontic.frame.access w v → ∀ c : Nat → T, (∀ n, c (n + 1) < c n) →
    (∃ x, Concrete x ∧ ContingentAt h.ontic v x ∧ h.IsAt v x (c 0)) →
    ∃ (signal : Nat → Option Nat) (issued : Nat → Prop),
      IndexAdmissible signal ∧ PositiveTrigger signal issued ∧
        Emission signal issued ∧ Forwarding signal

/-- Modal event-based causal finitism over momentary states: in every history
accessible from `w`, the state-causation relation `stateCause v` on moments
(`stateCause v s t`: the state of `v` at `s` is a direct cause of its state at
`t`) gives every moment finitely many distinct causal ancestors. -/
def StateCausalFinitism {W B T : Type} (h : History W B T)
    (stateCause : W → T → T → Prop) (w : W) : Prop :=
  ∀ v, h.ontic.frame.access w v → FiniteDistinctAncestry (stateCause v)

/-- Bridge from temporal precedence to causation: in every history accessible
from `w`, if a contingent concrete individual is present at `t`, the state at
every strictly earlier moment is a causal ancestor (along one or more
state-causation edges) of the state at `t`. -/
def PrecedenceIsStateCausation {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) (stateCause : W → T → T → Prop) (w : W) : Prop :=
  ∀ v, h.ontic.frame.access w v → ∀ x t s, Concrete x → ContingentAt h.ontic v x →
    h.IsAt v x t → s < t → Relation.TransGen (stateCause v) s t

/-- Temporal priority of grounds in history `v`: whenever `y` grounds a
contingent concrete individual `x` and `x` is present at `t`, `y` is present at
some strictly earlier moment. A ground present at all times satisfies it
unless `x` is present at a moment with nothing earlier. It
fails when some ground of `x` is not present at any moment before some moment
of `x`'s presence: in particular at a moment with nothing earlier, and for a
ground present only simultaneously, only later, or never. -/
def GroundsPrecedeAt {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) (grounds : W → B → B → Prop) (v : W) : Prop :=
  ∀ x y t, Concrete x → ContingentAt h.ontic v x → grounds v y x →
    h.IsAt v x t → ∃ s, s < t ∧ h.IsAt v y s

/-- Some history accessible from `w` has a contingent concrete individual
present at some moment, every contingent concrete individual of that history
has a concrete ground existing there (`EveryContingentGroundedAt`), and every
ground of a contingent concrete individual precedes it in time. -/
def PossiblyEarlierGroundedPopulated {W B T : Type} [Preorder T]
    (h : History W B T) (Concrete : B → Prop) (grounds : W → B → B → Prop)
    (w : W) : Prop :=
  ∃ v, h.ontic.frame.access w v ∧
    (∃ x t, Concrete x ∧ ContingentAt h.ontic v x ∧ h.IsAt v x t) ∧
    BruteFoundationBoundary.EveryContingentGroundedAt ⟨h.ontic, Concrete, grounds⟩ v ∧
    GroundsPrecedeAt h Concrete grounds v

/-- Some history accessible from `w` contains a necessary concrete individual:
one concrete individual exists there and at every world accessible from there
(`BruteFoundationBoundary.NecessaryConcreteAt` at that history). -/
def PossiblyNecessaryConcrete {W B T : Type} (h : History W B T)
    (Concrete : B → Prop) (grounds : W → B → B → Prop) (w : W) : Prop :=
  ∃ v, h.ontic.frame.access w v ∧
    BruteFoundationBoundary.NecessaryConcreteAt ⟨h.ontic, Concrete, grounds⟩ v

namespace Control

open TruthCore.Causality.InertEmptiness.Control (universal all rooted)
open TruthCore.Causality.ContingentComingToBe.Control (endless)

/-- No state causation at all. -/
def idleStates : Bool → Int → Int → Prop := fun _ _ _ => False

/-- Every earlier state directly causes every later one. -/
def precedenceStates : Bool → Int → Int → Prop := fun _ s t => s < t

/-- In the endless control, each individual is grounded by its predecessor. -/
def predecessorGrounds : Bool → Int → Int → Prop := fun _ y x => y = x - 1

/-- Simultaneous sustaining: individual `false` exists at both worlds and is
present at every time; individual `true` exists only at world `true`, is
present there at every time, and is grounded by `false`. -/
def sustained : History Bool Bool Nat where
  ontic := { frame := universal, ExistsAt := fun w x => x = false ∨ w = true,
             Causes := fun _ _ _ => False }
  IsAt := fun w x _ => x = false ∨ w = true
  now := 0

/-- `false` grounds `true`, and nothing else is grounded. -/
def sustainGrounds : Bool → Bool → Bool → Prop := fun _ y x => y = false ∧ x = true

/-- Mutual simultaneous grounding: two individuals exist only at world `true`,
are present there at every time, and each grounds the other. -/
def cycle : History Bool Bool Nat where
  ontic := { frame := universal, ExistsAt := fun w _ => w = true,
             Causes := fun _ _ _ => False }
  IsAt := fun w _ _ => w = true
  now := 0

/-- Each individual grounds the other. -/
def mutualGrounds : Bool → Bool → Bool → Prop := fun _ y x => y ≠ x

/-- State causation along the natural-number order. -/
def natPrecedenceStates : Bool → Nat → Nat → Prop := fun _ s t => s < t

/-- Later grounding: two individuals exist only at world `true`; `false` is
present there only at time 0, `true` from time 1 on. Each grounds the other, so
the ground of `false` is present only later, never simultaneously. -/
def laterGround : History Bool Bool Nat where
  ontic := { frame := universal, ExistsAt := fun w _ => w = true,
             Causes := fun _ _ _ => False }
  IsAt := fun w x t => w = true ∧ ((x = false ∧ t = 0) ∨ (x = true ∧ 1 ≤ t))
  now := 0

/-- Dense time with a first moment: the non-negative rationals. -/
abbrev DenseTime : Type := {q : ℚ // 0 ≤ q}

/-- The first moment of dense time. -/
def denseZero : DenseTime := ⟨0, le_refl 0⟩

/-- Dense coming-to-be: individual `false` exists at both worlds and is present
at every time; individual `true` exists only at world `true` and is present
there at every time after 0. -/
def densePast : History Bool Bool DenseTime where
  ontic := { frame := universal, ExistsAt := fun w x => x = false ∨ w = true,
             Causes := fun _ _ _ => False }
  IsAt := fun w x t => x = false ∨ (w = true ∧ 0 < t.1)
  now := denseZero

/-- Omission and nonvacuity controls, every individual counted concrete, two
mutually accessible worlds:
(1) endless generation with idle states: state-causal finitism holds, the
precedence bridge fails, and populated pasts are not founded;
(2) endless generation with every earlier state causing every later one: the
precedence bridge holds, finitism fails, populated pasts are not founded, and
the Reaper assembly bridge fails;
(3) endless generation grounded by predecessors: every contingent thing has an
earlier-present concrete ground, populated pasts are not founded, and founded
coming-to-be is not possible (the H2 replacement account);
(4) simultaneous sustaining by a necessary individual on natural-number time:
populated pasts are founded and every contingent thing is grounded, but
grounds do not precede, the contingent thing never came to be (H1), and
founded coming-to-be is not possible; a necessary concrete individual exists;
(5) mutual simultaneous grounding: populated pasts founded, presence gives
existence, inert emptiness, every contingent thing grounded, grounds do not
precede, H1, founded coming-to-be not possible, no necessary concrete
individual, and the grounding relation is not well-founded;
(6) the rooted control with `false` grounding `true`: every bridge and premise
of the new arguments holds together with founded coming-to-be;
(7) later grounding: populated pasts founded, every contingent thing grounded,
grounds do not precede, a contingent thing never came to be, no grounding edge
joins two individuals present at the same moment, and no necessary concrete
individual exists;
(8) dense time with a first moment: nothing precedes time 0, presence gives
existence, inert emptiness, every contingent thing comes to be, A3 (a
contingent-free moment before a populated one) holds, yet populated pasts are
not founded, founded coming-to-be is not possible, the Reaper bridge fails, and
no state-causation relation satisfies both finitism and the precedence bridge. -/
def Certificate : Prop :=
  (StateCausalFinitism endless idleStates true ∧
    ¬ PrecedenceIsStateCausation endless all idleStates true ∧
    ¬ PopulatedPastsFounded endless all true) ∧
  (PrecedenceIsStateCausation endless all precedenceStates true ∧
    ¬ StateCausalFinitism endless precedenceStates true ∧
    ¬ ReaperAssembly endless all true) ∧
  (BruteFoundationBoundary.EveryContingentGroundedAt
      ⟨endless.ontic, all, predecessorGrounds⟩ true ∧
    GroundsPrecedeAt endless all predecessorGrounds true ∧
    ¬ PossiblyFoundedComingToBe endless all true) ∧
  (PopulatedPastsFounded sustained all true ∧
    BruteFoundationBoundary.EveryContingentGroundedAt
      ⟨sustained.ontic, all, sustainGrounds⟩ true ∧
    ¬ GroundsPrecedeAt sustained all sustainGrounds true ∧
    ¬ AllContingentsComeToBeAt sustained all true ∧
    ¬ PossiblyFoundedComingToBe sustained all true ∧
    BruteFoundationBoundary.NecessaryConcreteAt
      ⟨sustained.ontic, all, sustainGrounds⟩ true) ∧
  (PopulatedPastsFounded cycle all true ∧
    CountTemporalNecessity.HistoryPresenceActual cycle ∧
    EmptinessStaysEmpty cycle all ∧
    BruteFoundationBoundary.EveryContingentGroundedAt
      ⟨cycle.ontic, all, mutualGrounds⟩ true ∧
    ¬ GroundsPrecedeAt cycle all mutualGrounds true ∧
    ¬ AllContingentsComeToBeAt cycle all true ∧
    ¬ PossiblyFoundedComingToBe cycle all true ∧
    ¬ BruteFoundationBoundary.NecessaryConcreteAt
      ⟨cycle.ontic, all, mutualGrounds⟩ true ∧
    ¬ WellFounded (mutualGrounds true)) ∧
  (ReaperAssembly rooted all true ∧
    StateCausalFinitism rooted natPrecedenceStates true ∧
    PrecedenceIsStateCausation rooted all natPrecedenceStates true ∧
    PopulatedPastsFounded rooted all true ∧
    PossiblyEarlierGroundedPopulated rooted all sustainGrounds true ∧
    PossiblyFoundedComingToBe rooted all true) ∧
  (PopulatedPastsFounded laterGround all true ∧
    BruteFoundationBoundary.EveryContingentGroundedAt
      ⟨laterGround.ontic, all, mutualGrounds⟩ true ∧
    ¬ GroundsPrecedeAt laterGround all mutualGrounds true ∧
    ¬ AllContingentsComeToBeAt laterGround all true ∧
    (∀ x y t, mutualGrounds true y x →
      ¬ (laterGround.IsAt true x t ∧ laterGround.IsAt true y t)) ∧
    ¬ BruteFoundationBoundary.NecessaryConcreteAt
      ⟨laterGround.ontic, all, mutualGrounds⟩ true) ∧
  ((∀ s : DenseTime, ¬ s < denseZero) ∧
    CountTemporalNecessity.HistoryPresenceActual densePast ∧
    EmptinessStaysEmpty densePast all ∧
    AllContingentsComeToBeAt densePast all true ∧
    PossiblyContingentsAbsentThenPresent densePast all true ∧
    ¬ PopulatedPastsFounded densePast all true ∧
    ¬ PossiblyFoundedComingToBe densePast all true ∧
    ¬ ReaperAssembly densePast all true ∧
    ∀ stateCause : Bool → DenseTime → DenseTime → Prop,
      ¬ (StateCausalFinitism densePast stateCause true ∧
        PrecedenceIsStateCausation densePast all stateCause true))

end Control

end TruthCore.Causality.ComingToBeHorns
