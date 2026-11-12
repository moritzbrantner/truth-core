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

**Two typed senses (disambiguation BEGINS).** Both constrain the *time* before
the populated moments of a history, not contingent reality itself. History `v`
has a populated moment (some contingent concrete individual present) and

* BEGINS_1 (`FirstMomentBeginningAt`): the time before every populated moment
  of `v` has a first moment (`BegunComingToBe.BegunAt`); or
* BEGINS_2 (`FiniteDurationBeginningAt`): the time before every populated
  moment of `v` is of finite duration on the supplied clock
  (`MetricGrimReaper.MetricallyFinitePast`); the intended clock is CLOCK_1.
  With a bounded clock every past is finite and BEGINS_2 reduces to population.

Examples. Discrete or continuous time with a first moment satisfies both. A
populated history whose time is open below and of finite duration (the order
and metric shape of standard FLRW cosmic time: the initial singularity is not a
moment) satisfies BEGINS_2 and not BEGINS_1 (`Control.Certificate` 2). An
endless succession of populated days satisfies neither (`Control.Certificate`
1). Non-examples showing that these are senses about time, not about the
beginning of contingent reality: integer time, empty before `0` and populated
from `0` on, satisfies neither, although contingent reality began a finite time
ago; non-negative real time, empty at `0` and populated after it, satisfies
BEGINS_1 although there is no first populated moment. A third sense, a first
populated moment after emptiness (related to premise A3 of Arrival A), is not
formalized here. In linear time BEGINS_1 gives BEGINS_2
(`possiblyFiniteDurationOfFirstMoment`). Neither is the individual coming-to-be
of `TemporalHistory.BeginsAt`, nor an empty first state.

**The metric Scenario.** `finiteDurationScenario` instantiates the Scenario's
beginning predicate with BEGINS_2 and leaves its totality-cause relation a
parameter. B1 in sense BEGINS_2 (`PossiblyBeginsFiniteDuration`) and B2 in
sense BEGINS_2 (`FiniteDurationCausalOpportunity`) are separate statements from
the parameter-sense B1 and B2, so the senses cannot be exchanged silently.
Because the cause relation is unconstrained, B2 for any relation gives B2 for
the relation that always holds (`trivialCauseOpportunity` in the results),
and the arrival needs only the latter: the content B2 contributes is that,
given B1, possibly a BEGINS_2 history contains an existing concrete individual
outside the contingent totality. The cause conjunct does no logical work.

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
some moment, and the time before every moment at which one is present has a
first moment. A constraint on time, not on when contingent reality began. -/
def FirstMomentBeginningAt {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) (v : W) : Prop :=
  (∃ t, PopulatedAt h Concrete v t) ∧ ∀ t, PopulatedAt h Concrete v t → BegunAt t

/-- BEGINS_2: in history `v` some contingent concrete individual is present at
some moment, and the time before every moment at which one is present is of
finite duration on the clock `k`. A constraint on time, not on when contingent
reality began. -/
def FiniteDurationBeginningAt {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) (k : TimeClock T) (v : W) : Prop :=
  (∃ t, PopulatedAt h Concrete v t) ∧
    ∀ t, PopulatedAt h Concrete v t → MetricallyFinitePast k t

/-- B1 in sense BEGINS_1: possibly, a populated history in which the time
before every populated moment has a first moment. -/
def PossiblyBeginsFirstMoment {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) (w : W) : Prop :=
  ∃ v, h.ontic.frame.access w v ∧ FirstMomentBeginningAt h Concrete v

/-- B1 in sense BEGINS_2: possibly, a populated history in which the time
before every populated moment is of finite duration on the clock `k`. -/
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

/-- B2 in sense BEGINS_2: if some accessible history is a BEGINS_2 history with
a contingent concrete individual, then some accessible history is one in which,
moreover, some existing concrete individual, distinct from every contingent
concrete individual there, stands in the supplied totality-cause relation. The
relation is an unconstrained parameter: nothing makes it causal. -/
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
(2) in `openBelow` (positive real times, identity clock): Euclidean access and
reflexivity at `true` hold, B1 holds in sense BEGINS_2 and fails in sense
BEGINS_1, the causal opportunity premise in sense BEGINS_2 fails for the empty
totality-cause relation, and for every grounding relation no concrete
individual is necessary at either world;
(3) in `openBelowSource`, with `none` the totality cause at world `true`, B1
and B2 in sense BEGINS_2, Euclidean access and reflexivity at `true` all hold,
together with a necessary concrete individual at `true`. -/
def Certificate : Prop :=
  (PossiblyPopulated pivot all 1 ∧ ¬ PossiblyBeginsFiniteDuration pivot all intClock 1) ∧
  (ActualEuclidean.EuclideanAt openBelow.ontic.frame true ∧
    NecessarilyUnderived.ActualReflexive openBelow.ontic true ∧
    PossiblyBeginsFiniteDuration openBelow all posClock true ∧
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
