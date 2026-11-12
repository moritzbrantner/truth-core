module

public import TruthCore.Causality.MetricGrimReaper
public import TruthCore.Causality.PossibleCauseOfContingency
public import TruthCore.Causality.ActualEuclidean
public import TruthCore.Causality.ComingToBeHorns

/-!
# Two senses of "contingent concrete reality begins", and Arrival B in the metric one

Analyst formulation for the modal spine to "God exists"
(`docs/notes/modal-spine.md`, Arrival B, premise B1). Attribution deferred.

**What B1 says now.** The existing premise B1
(`PossibleCauseOfContingency.PossiblyBeginsAt`) is stated for a `Scenario`
whose field `beginsContingency : World → Prop` is an *uninterpreted parameter*:
the Scenario has no times, and "begins" is whatever predicate is supplied.
`LocalFramePossibleExternalCause.necessaryConcrete` and
`ActualEuclidean.externalNecessaryConcrete` hold for every such predicate,
including the constant `True` (the existing controls use it). So B1 as typed
fixes no sense of beginning, and the arrival's validity does not depend on one;
the content of B1 and of the causal-opportunity premise B2 depends on the
predicate supplied.

**Two senses (disambiguation BEGINS).** Over a `History` with an order of
moments, contingent concrete reality *begins* in history `v` when some
contingent concrete individual is present at some moment of `v` and

* BEGINS_1 (`FirstMomentBeginningAt`): every moment at which a contingent
  concrete individual is present in `v` has a past with a first moment
  (`BegunComingToBe.BegunAt`); or
* BEGINS_2 (`FiniteDurationBeginningAt`): every such moment has a past of
  finite duration on the supplied clock (`MetricGrimReaper.MetricallyFinitePast`),
  read with the physically privileged clock CLOCK_1: contingent concrete
  reality began a finite time ago.

Examples. Discrete or continuous time with a first moment satisfies both. A
populated history whose time is open below and of finite duration (the order
and metric shape of standard FLRW cosmic time: the initial singularity is not a
moment) satisfies BEGINS_2 and not BEGINS_1 (`Control.Certificate` 2). An
endless succession of days satisfies neither (`Control.Certificate` 1).
In linear time BEGINS_1 gives BEGINS_2 (`possiblyFiniteDurationOfFirstMoment`).
Neither is the individual coming-to-be of `TemporalHistory.BeginsAt` (one
individual present at `t` and absent before), nor an empty first state:
BEGINS_2 says nothing about any empty moment.

**The metric Scenario.** `finiteDurationScenario` instantiates the Scenario's
beginning predicate with BEGINS_2; the possibility of a BEGINS_2 beginning
(`PossiblyBeginsFiniteDuration`, B1 in sense BEGINS_2) and the causal
opportunity for it (`FiniteDurationCausalOpportunity`, B2 in sense BEGINS_2)
are separate statements from the parameter-sense B1 and B2, so the two senses
cannot be exchanged silently.

Applicability of every definition below to reality remains OPEN.
-/

@[expose] public section

namespace TruthCore.Causality.MetricBeginningArrival

open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Modal.TemporalHistory
open TruthCore.Causality.BegunComingToBe (BegunAt)
open TruthCore.Causality.GrimReaperPatchwork (PopulatedAt)
open TruthCore.Causality.MetricGrimReaper
open TruthCore.Causality.PossibleCauseOfContingency

/-- BEGINS_1: in history `v` some contingent concrete individual is present at
some moment, and every moment at which one is present has a past with a first
moment. -/
def FirstMomentBeginningAt {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) (v : W) : Prop :=
  (∃ t, PopulatedAt h Concrete v t) ∧ ∀ t, PopulatedAt h Concrete v t → BegunAt t

/-- BEGINS_2: in history `v` some contingent concrete individual is present at
some moment, and every moment at which one is present has a past of finite
duration on the clock `k`. -/
def FiniteDurationBeginningAt {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) (k : TimeClock T) (v : W) : Prop :=
  (∃ t, PopulatedAt h Concrete v t) ∧
    ∀ t, PopulatedAt h Concrete v t → MetricallyFinitePast k t

/-- Possibly, contingent concrete reality begins in sense BEGINS_1. -/
def PossiblyBeginsFirstMoment {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) (w : W) : Prop :=
  ∃ v, h.ontic.frame.access w v ∧ FirstMomentBeginningAt h Concrete v

/-- B1 in sense BEGINS_2: possibly, contingent concrete reality began a finite
time ago. -/
def PossiblyBeginsFiniteDuration {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) (k : TimeClock T) (w : W) : Prop :=
  ∃ v, h.ontic.frame.access w v ∧ FiniteDurationBeginningAt h Concrete k v

/-- Possibly, some contingent concrete individual is present at some moment:
some history accessible from `w` is populated. No beginning, duration or
cause is mentioned. -/
def PossiblyPopulated {W B T : Type} (h : History W B T) (Concrete : B → Prop)
    (w : W) : Prop :=
  ∃ v, h.ontic.frame.access w v ∧ ∃ t, PopulatedAt h Concrete v t

/-- The Scenario of `PossibleCauseOfContingency` over a history, with the
beginning predicate instantiated by BEGINS_2 and a supplied totality-cause
relation. Ontic, concreteness and the cause relation are those supplied. -/
def finiteDurationScenario {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) (k : TimeClock T) (causes : W → B → Prop) : Scenario W B where
  ontic := h.ontic
  concrete := Concrete
  beginsContingency := FiniteDurationBeginningAt h Concrete k
  causesContingencyTotality := causes

/-- B2 in sense BEGINS_2: if contingent concrete reality can begin a finite
time ago, then in some accessible history it does so and some existing
concrete individual, distinct from every contingent concrete individual there,
stands in the supplied totality-cause relation there. -/
def FiniteDurationCausalOpportunity {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) (k : TimeClock T) (causes : W → B → Prop) (w : W) : Prop :=
  CausalOpportunityAt (finiteDurationScenario h Concrete k causes) w

namespace Control

open TruthCore.Causality.MetricGrimReaper.Control (PosReal posClock intClock openBelow)
open TruthCore.Causality.GrimReaperPatchwork.Control (pivot)
open TruthCore.Causality.InertEmptiness.Control (all)

/-- `openBelow` with one more individual, `none`, existing at both worlds and
present at no moment; individual `some n` exists and is present at every
moment exactly at world `true`. Times are the positive reals. -/
def openBelowSource : History Bool (Option Int) PosReal where
  ontic := { frame := TruthCore.Causality.InertEmptiness.Control.universal,
             ExistsAt := fun w x => match x with
               | none => True
               | some _ => w = true,
             Causes := fun _ _ _ => False }
  IsAt := fun w x _ => match x with
    | none => False
    | some _ => w = true
  now := ⟨1, one_pos⟩

/-- Every individual counts as concrete:
(1) in the beginningless integer history `pivot` (identity clock) contingent
concrete things are possibly present, and no accessible history begins in
sense BEGINS_2;
(2) in `openBelow` (positive real times, identity clock): B1 holds in sense
BEGINS_2 and fails in sense BEGINS_1, the causal opportunity premise in sense
BEGINS_2 fails for the empty totality-cause relation, and for every grounding
relation no concrete individual is necessary at either world;
(3) in `openBelowSource`, with `none` the totality cause at world `true`, B1
and B2 in sense BEGINS_2, Euclidean access and reflexivity at `true` all hold,
together with a necessary concrete individual at `true`. -/
def Certificate : Prop :=
  (PossiblyPopulated pivot all 1 ∧ ¬ PossiblyBeginsFiniteDuration pivot all intClock 1) ∧
  (PossiblyBeginsFiniteDuration openBelow all posClock true ∧
    ¬ PossiblyBeginsFirstMoment openBelow all true ∧
    ¬ FiniteDurationCausalOpportunity openBelow all posClock (fun _ _ => False) true ∧
    (∀ G v, ¬ BruteFoundationBoundary.NecessaryConcreteAt ⟨openBelow.ontic, all, G⟩ v)) ∧
  (PossiblyBeginsFiniteDuration openBelowSource all posClock true ∧
    FiniteDurationCausalOpportunity openBelowSource all posClock
      (fun w c => w = true ∧ c = none) true ∧
    ActualEuclidean.EuclideanAt openBelowSource.ontic.frame true ∧
    NecessarilyUnderived.ActualReflexive openBelowSource.ontic true ∧
    ∀ G, BruteFoundationBoundary.NecessaryConcreteAt ⟨openBelowSource.ontic, all, G⟩ true)

end Control

end TruthCore.Causality.MetricBeginningArrival
