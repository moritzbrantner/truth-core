module

public import TruthCore.Causality.MetricBeginningArrival
public import TruthCore.Results.Causality.MetricGrimReaper.Solution
public import TruthCore.Results.Causality.ActualEuclidean.Solution

@[expose] public section

namespace TruthCore.Results.Causality.MetricBeginningArrival
open TruthCore.Causality.MetricBeginningArrival
open TruthCore.Causality.MetricGrimReaper
open TruthCore.Causality.GrimReaperPatchwork (PopulatedAt)
open TruthCore.Causality.PossibleCauseOfContingency
open TruthCore.Causality.ActualEuclidean (EuclideanAt)
open TruthCore.Causality.NecessarilyUnderived (ActualReflexive)
open TruthCore.German.Kant.CosmologicalInference (ContingentAt NecessaryAt)
open TruthCore.Modal.TemporalHistory (History)

/-- B1 in sense BEGINS_2 from metrically finite populated pasts: a possibly
populated history is accessible, and every populated moment of every accessible
history has a past of finite duration, so that history began a finite time
ago. -/
theorem possiblyBeginsFiniteDurationOfMetricallyFinite {W B T : Type} [Preorder T]
    (h : History W B T) (Concrete : B → Prop) (k : TimeClock T) (w : W)
    (hFinite : PopulatedPastsMetricallyFinite h Concrete k w)
    (hPopulated : PossiblyPopulated h Concrete w) :
    PossiblyBeginsFiniteDuration h Concrete k w := by
  obtain ⟨v, hwv, t, hPop⟩ := hPopulated
  refine ⟨v, hwv, ⟨t, hPop⟩, ?_⟩
  rintro s ⟨x, hx, hCont, hxs⟩
  exact hFinite v hwv x s hx hCont hxs

/-- Strength order (linear time, any real clock): a possible BEGINS_1 beginning
is a possible BEGINS_2 beginning, since a past with a first moment has finite
duration. -/
theorem possiblyFiniteDurationOfFirstMoment {W B T : Type} [LinearOrder T]
    (h : History W B T) (Concrete : B → Prop) (k : TimeClock T) (w : W)
    (hFirst : PossiblyBeginsFirstMoment h Concrete w) :
    PossiblyBeginsFiniteDuration h Concrete k w := by
  obtain ⟨v, hwv, hSome, hAll⟩ := hFirst
  exact ⟨v, hwv, hSome, fun t hPop =>
    TruthCore.Results.Causality.MetricGrimReaper.metricallyFiniteOfBegun k t (hAll t hPop)⟩

/-- A BEGINS_2 beginning of a history is a beginning of its metric Scenario. -/
theorem possiblyBeginsAtOfFiniteDuration {W B T : Type} [Preorder T]
    (h : History W B T) (Concrete : B → Prop) (k : TimeClock T)
    (causes : W → B → Prop) (w : W)
    (hBegins : PossiblyBeginsFiniteDuration h Concrete k w) :
    PossiblyBeginsAt (finiteDurationScenario h Concrete k causes) w := by
  obtain ⟨v, hwv, hB⟩ := hBegins
  obtain ⟨⟨_, x, hx, hCont, _⟩, _⟩ := id hB
  exact ⟨v, hwv, hB, x, hx, hCont⟩

/-- Arrival B in sense BEGINS_2, with Euclidean access at the selected world
only. Reuses `ActualEuclidean.externalNecessaryConcrete` on the metric
Scenario; the grounding field of the conclusion's profile is an arbitrary
parameter. -/
theorem necessaryConcreteOfFiniteDurationBeginning {W B T : Type} [Preorder T]
    (h : History W B T) (Concrete : B → Prop) (k : TimeClock T)
    (causes : W → B → Prop) (G : W → B → B → Prop) (w : W)
    (hEuclidean : EuclideanAt h.ontic.frame w)
    (hReflexive : ActualReflexive h.ontic w)
    (hBegins : PossiblyBeginsFiniteDuration h Concrete k w)
    (hOpportunity : FiniteDurationCausalOpportunity h Concrete k causes w) :
    TruthCore.Causality.BruteFoundationBoundary.NecessaryConcreteAt
      ⟨h.ontic, Concrete, G⟩ w :=
  TruthCore.Results.Causality.ActualEuclidean.externalNecessaryConcrete
    (finiteDurationScenario h Concrete k causes) w hEuclidean hReflexive
    (possiblyBeginsAtOfFiniteDuration h Concrete k causes w hBegins) hOpportunity

/-- B1 and B2 in sense BEGINS_2 already give the possibility of a necessary
concrete individual, with no frame condition: the external cause in the
accessible history is necessary there. -/
theorem possiblyNecessaryOfFiniteDurationOpportunity {W B T : Type} [Preorder T]
    (h : History W B T) (Concrete : B → Prop) (k : TimeClock T)
    (causes : W → B → Prop) (G : W → B → B → Prop) (w : W)
    (hBegins : PossiblyBeginsFiniteDuration h Concrete k w)
    (hOpportunity : FiniteDurationCausalOpportunity h Concrete k causes w) :
    TruthCore.Causality.ComingToBeHorns.PossiblyNecessaryConcrete h Concrete G w := by
  obtain ⟨v, hwv, _, c, hc, he, _, hOutside⟩ :=
    hOpportunity (possiblyBeginsAtOfFiniteDuration h Concrete k causes w hBegins)
  exact ⟨v, hwv, c, hc, he,
    TruthCore.Causality.LocalFramePossibleExternalCause.necessaryOfExternalCandidate
      (finiteDurationScenario h Concrete k causes) v c hc he hOutside⟩

open TruthCore.Causality.MetricBeginningArrival.Control
open TruthCore.Causality.MetricGrimReaper.Control (PosReal posClock intClock openBelow)
open TruthCore.Causality.GrimReaperPatchwork.Control (pivot)
open TruthCore.Causality.InertEmptiness.Control (all)
open TruthCore.Results.Causality.MetricGrimReaper (posFinite posNotBegun openBelowContingent
  unboundedOfSpaced)
open TruthCore.Results.Causality.GrimReaperPatchwork (pivotOne pivotPopulated)

/-- No integer moment has a past of finite duration on the identity clock. -/
theorem intNotFinite (t : Int) : ¬ MetricallyFinitePast intClock t := by
  intro hFin
  have hDesc : TruthCore.Causality.GrimReaperPatchwork.Descent
      (fun n : Nat => t - (n : Int)) := by
    intro n; push_cast; omega
  have hSlots : SlotsAtLeast intClock (fun n : Nat => t - (n : Int)) := by
    refine ⟨1, one_pos, fun n => ?_⟩
    show (1 : ℝ) ≤ ((t - (n : Int) : Int) : ℝ) - ((t - ((n + 1 : Nat) : Int) : Int) : ℝ)
    push_cast; linarith
  exact unboundedOfSpaced intClock _ hDesc hSlots (by simpa using hFin)

theorem openBelowSourceContingent (n : Int) :
    ContingentAt openBelowSource.ontic true (some n) :=
  ⟨rfl, false, trivial, Bool.false_ne_true⟩

/-- Independence, nonvacuity and sense controls. -/
theorem controls : Certificate := by
  refine ⟨⟨⟨1, trivial, 0, pivotPopulated⟩, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · rintro ⟨v, _, ⟨t, hPop⟩, hAll⟩
    exact intNotFinite t (hAll t hPop)
  · exact ⟨true, trivial, ⟨⟨1, one_pos⟩, 0, trivial, openBelowContingent 0, rfl⟩,
      fun t _ => posFinite t⟩
  · rintro ⟨v, _, ⟨t, hPop⟩, hAll⟩
    exact posNotBegun t (hAll t hPop)
  · intro hOpp
    have hB : PossiblyBeginsFiniteDuration openBelow all posClock true :=
      ⟨true, trivial, ⟨⟨1, one_pos⟩, 0, trivial, openBelowContingent 0, rfl⟩,
        fun t _ => posFinite t⟩
    obtain ⟨_, _, _, _, _, _, hc, _⟩ :=
      hOpp (possiblyBeginsAtOfFiniteDuration _ _ _ _ _ hB)
    exact hc
  · rintro G v ⟨c, _, _, hn⟩
    have hFalse : openBelow.ontic.ExistsAt false c := hn false trivial
    exact Bool.false_ne_true hFalse
  · exact ⟨true, trivial, ⟨⟨1, one_pos⟩, some 0, trivial, openBelowSourceContingent 0, rfl⟩,
      fun t _ => posFinite t⟩
  · intro _
    have hPop : PopulatedAt openBelowSource all true (⟨1, one_pos⟩ : PosReal) :=
      ⟨some 0, trivial, openBelowSourceContingent 0, rfl⟩
    have hBegins : FiniteDurationBeginningAt openBelowSource all posClock true :=
      ⟨⟨_, hPop⟩, fun t _ => posFinite t⟩
    refine ⟨true, trivial, ⟨hBegins, some 0, trivial, openBelowSourceContingent 0⟩,
      none, trivial, trivial, ⟨rfl, rfl⟩, ?_⟩
    intro x _ hCont hEq
    subst hEq
    obtain ⟨_, _, _, hAbsent⟩ := hCont
    exact hAbsent trivial
  · intro _ _ _ _
    trivial
  · trivial
  · intro G
    exact ⟨none, trivial, trivial, fun _ _ => trivial⟩

end TruthCore.Results.Causality.MetricBeginningArrival
