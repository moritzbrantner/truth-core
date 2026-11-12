module

public import TruthCore.Causality.GrimReaperPatchwork
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Basic.NNReal.Defs

/-!
# A metric Grim Reaper: stations in slots of at least a fixed length

Analyst formulation for the modal spine to "God exists"
(`docs/notes/modal-spine.md`, horn H2 of the initial-state rival). Attribution
deferred: nothing here is claimed to be Koons's or Pruss's exact principle.

`GrimReaperPatchwork` states the Reaper premises over descents of moments that
are purely order-theoretic. `(0, t]` and `(-∞, t]` are order-isomorphic, so its
coinitial premises cannot tell a metrically finite past with no first moment
(standard FLRW cosmology) from a metrically infinite one, and its unrestricted
premises place stations in the shrinking slots `t, t/2, t/4, …` of continuous
time with a first moment (the setting of the Benardete paradoxes). This module
adds the missing metric and restricts both premises to descents whose
consecutive slots are at least some fixed positive length.

**Metric.** A `TimeClock` is a real-valued time coordinate that strictly
increases along the order of moments (Mathlib `StrictMono`). The duration from
`s` to a later `t` is `reading t - reading s`. FLRW cosmic time, a Newtonian
absolute time, and the identity on `ℤ`, `ℝ`, `ℝ≥0` or the positive reals are
clocks. The past of `t` is *metrically finite* when the readings of the moments
at or before `t` are bounded below (Mathlib `BddBelow`), and metrically infinite
otherwise. Examples: in `(0, ∞)` and `[0, ∞)` every past is metrically finite;
in `ℤ` or `ℝ` none is. A clock is one coordinate for the whole frame: every
world of a `History` shares its order of moments and, here, its clock. A frame
whose worlds carry different metrics needs a world-indexed clock, which is not
built. No dynamics, curvature or proper time along particular worldlines is
encoded.

**Spaced descent.** `SlotsAtLeast k c`: some `δ > 0` bounds every slot
`reading (c n) - reading (c (n + 1))` from below (one station per past day,
say). A spaced descent from `t` exists exactly when, in linear time, the past of
`t` is metrically infinite (`Solution`: `unboundedOfSpaced`,
`spacedDescentOfUnbounded`). So the spaced premises say nothing about any
metrically finite past, with or without a first moment.

**Premises.** The local pieces (`PieceAt`, the four rules of
`GrimReaperPatchwork`) and the patchwork premise are unchanged; only their range
of descents is restricted to spaced descents below populated moments. The
conclusion, `PopulatedPastsMetricallyFinite`, says that in every accessible
history every moment with a contingent concrete thing present has a metrically
finite past. It does not say the past has a beginning: an open-below, finite
past is allowed (`Control.openBelow`).

Applicability of every definition below to reality remains OPEN.
-/

@[expose] public section

namespace TruthCore.Causality.MetricGrimReaper

open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Modal.TemporalHistory
open TruthCore.Causality.BegunComingToBe
open TruthCore.Causality.GrimReaperPatchwork

/-- A real time coordinate strictly increasing along the order of moments.
Durations are differences of readings. -/
structure TimeClock (T : Type) [Preorder T] where
  reading : T → ℝ
  strictMono : StrictMono reading

/-- The past of `t` (the moments at or before it) has bounded-below readings:
it has finite duration. -/
def MetricallyFinitePast {T : Type} [Preorder T] (k : TimeClock T) (t : T) : Prop :=
  BddBelow (k.reading '' Set.Iic t)

/-- Every slot between consecutive members of `c` lasts at least some fixed
positive duration. -/
def SlotsAtLeast {T : Type} [Preorder T] (k : TimeClock T) (c : Nat → T) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ n, δ ≤ k.reading (c n) - k.reading (c (n + 1))

/-- Local Reaper pieces along spaced descents: in every history `v` accessible
from `w`, along every strictly descending sequence of moments with slots of at
least a fixed positive length, starting at a populated moment, every two
adjacent pieces are co-possible. -/
def SpacedReaperPiecesPossible {W B T : Type} [Preorder T] (R : ReaperFrame W T)
    (h : History W B T) (Concrete : B → Prop) (k : TimeClock T) (w : W) : Prop :=
  ∀ v, h.ontic.frame.access w v → ∀ c : Nat → T, Descent c → SlotsAtLeast k c →
    PopulatedAt h Concrete v (c 0) → AdjacentPiecesCoPossible R h v c

/-- Reaper patchwork along spaced descents: in every history `v` accessible
from `w`, along every strictly descending sequence of moments with slots of at
least a fixed positive length, starting at a populated moment, if every two
adjacent pieces are co-possible, the whole arrangement is possible. -/
def SpacedReaperPatchwork {W B T : Type} [Preorder T] (R : ReaperFrame W T)
    (h : History W B T) (Concrete : B → Prop) (k : TimeClock T) (w : W) : Prop :=
  ∀ v, h.ontic.frame.access w v → ∀ c : Nat → T, Descent c → SlotsAtLeast k c →
    PopulatedAt h Concrete v (c 0) →
    AdjacentPiecesCoPossible R h v c → ArrangementPossible R h v c

/-- In every history accessible from `w`, every moment at which some contingent
concrete individual is present has a metrically finite past. -/
def PopulatedPastsMetricallyFinite {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) (k : TimeClock T) (w : W) : Prop :=
  ∀ v, h.ontic.frame.access w v → ∀ x t, Concrete x → ContingentAt h.ontic v x →
    h.IsAt v x t → MetricallyFinitePast k t

namespace Control

/-- Positive real times: open below, every past metrically finite. -/
abbrev PosReal : Type := {x : ℝ // 0 < x}

/-- The integers as their own real clock. -/
noncomputable def intClock : TimeClock Int := ⟨fun t => (t : ℝ), Int.cast_strictMono⟩

/-- The positive reals as their own clock. -/
def posClock : TimeClock PosReal := ⟨fun t => t.1, fun _ _ h => h⟩

/-- The non-negative reals as their own clock. -/
def nnClock : TimeClock NNReal := ⟨fun t => (t : ℝ), fun _ _ h => h⟩

/-- An open-below, metrically finite populated past (the order and metric shape
of standard FLRW cosmic time, nothing more): times are the positive reals,
worlds booleans, individuals integers. At world `true` every individual exists
and is present at every moment; at world `false` nothing exists. -/
def openBelow : History Bool Int PosReal where
  ontic := { frame := TruthCore.Causality.InertEmptiness.Control.universal,
             ExistsAt := fun w _ => w = true, Causes := fun _ _ _ => False }
  IsAt := fun w _ _ => w = true
  now := ⟨1, one_pos⟩

/-- Continuous time with a first moment: times are the non-negative reals. At
world `true` one individual exists and is present at every moment after `0`,
and absent at `0`; at world `false` nothing exists. -/
def firstMoment : History Bool Unit NNReal where
  ontic := { frame := TruthCore.Causality.InertEmptiness.Control.universal,
             ExistsAt := fun w _ => w = true, Causes := fun _ _ _ => False }
  IsAt := fun w _ t => w = true ∧ 0 < t
  now := 1

open TruthCore.Causality.InertEmptiness.Control (all)
open TruthCore.Causality.GrimReaperPatchwork.Control (pivot quietFrame pivotFrame)
open TruthCore.Causality.BegunComingToBe.Control (predecessorGrounds)

/-- Independence, nonvacuity and reach controls, every individual counted
concrete:
(1) in the beginningless integer history `pivot` with the identity clock,
silent registers satisfy spaced patchwork but not spaced local pieces, pivot
registers satisfy spaced local pieces but not spaced patchwork, and not every
populated past is metrically finite;
(2) in `openBelow` (positive real times), for every register frame both spaced
premises hold and the coinitial local-pieces and patchwork premises do not both
hold; every populated past is metrically finite and not every one is begun; beginningless
populated pasts have coinitial descents; the earlier-grounded possibility
premise holds; and begun coming-to-be is not possible;
(3) in `firstMoment` (non-negative real times, nothing present at `0`), for
every register frame both spaced premises hold and the unrestricted local-pieces
and patchwork premises do not both hold; populated pasts are metrically finite
and begun, not every one founded; and begun coming-to-be is possible. -/
def Certificate : Prop :=
  (SpacedReaperPatchwork (quietFrame Int Int) pivot all intClock 1 ∧
    ¬ SpacedReaperPiecesPossible (quietFrame Int Int) pivot all intClock 1 ∧
    SpacedReaperPiecesPossible pivotFrame pivot all intClock 1 ∧
    ¬ SpacedReaperPatchwork pivotFrame pivot all intClock 1 ∧
    ¬ PopulatedPastsMetricallyFinite pivot all intClock 1) ∧
  ((∀ R : ReaperFrame Bool PosReal,
      SpacedReaperPiecesPossible R openBelow all posClock true ∧
      SpacedReaperPatchwork R openBelow all posClock true ∧
      ¬ (CoinitialReaperPiecesPossible R openBelow all true ∧
        CoinitialReaperPatchwork R openBelow all true)) ∧
    PopulatedPastsMetricallyFinite openBelow all posClock true ∧
    ¬ PopulatedPastsBegun openBelow all true ∧
    BeginninglessPastsCountablyCoinitial openBelow all true ∧
    ComingToBeHorns.PossiblyEarlierGroundedPopulated openBelow all
      predecessorGrounds true ∧
    ¬ PossiblyBegunComingToBe openBelow all true) ∧
  ((∀ R : ReaperFrame Bool NNReal,
      SpacedReaperPiecesPossible R firstMoment all nnClock true ∧
      SpacedReaperPatchwork R firstMoment all nnClock true ∧
      ¬ (ReaperPiecesPossible R firstMoment all true ∧
        ReaperPatchwork R firstMoment all true)) ∧
    PopulatedPastsMetricallyFinite firstMoment all nnClock true ∧
    PopulatedPastsBegun firstMoment all true ∧
    ¬ ComingToBeHorns.PopulatedPastsFounded firstMoment all true ∧
    PossiblyBegunComingToBe firstMoment all true)

end Control

end TruthCore.Causality.MetricGrimReaper
