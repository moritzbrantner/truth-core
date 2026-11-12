import TruthCore.Causality.MetricBeginningArrival
import TruthCore.Results.Causality.MetricGrimReaper.Solution
import TruthCore.Results.Causality.ActualEuclidean.Solution

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
  sorry

/-- Strength order (linear time, any real clock): a possible BEGINS_1 beginning
is a possible BEGINS_2 beginning, since a past with a first moment has finite
duration. -/
theorem possiblyFiniteDurationOfFirstMoment {W B T : Type} [LinearOrder T]
    (h : History W B T) (Concrete : B → Prop) (k : TimeClock T) (w : W)
    (hFirst : PossiblyBeginsFirstMoment h Concrete w) :
    PossiblyBeginsFiniteDuration h Concrete k w := by
  sorry

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
      ⟨h.ontic, Concrete, G⟩ w := by
  sorry

/-- B1 and B2 in sense BEGINS_2 already give the possibility of a necessary
concrete individual, with no frame condition: the external cause in the
accessible history is necessary there. -/
theorem possiblyNecessaryOfFiniteDurationOpportunity {W B T : Type} [Preorder T]
    (h : History W B T) (Concrete : B → Prop) (k : TimeClock T)
    (causes : W → B → Prop) (G : W → B → B → Prop) (w : W)
    (hBegins : PossiblyBeginsFiniteDuration h Concrete k w)
    (hOpportunity : FiniteDurationCausalOpportunity h Concrete k causes w) :
    TruthCore.Causality.ComingToBeHorns.PossiblyNecessaryConcrete h Concrete G w := by
  sorry

open TruthCore.Causality.MetricBeginningArrival.Control
open TruthCore.Causality.MetricGrimReaper.Control (PosReal posClock intClock openBelow)
open TruthCore.Causality.GrimReaperPatchwork.Control (pivot)
open TruthCore.Causality.InertEmptiness.Control (all)
open TruthCore.Results.Causality.MetricGrimReaper (posFinite posNotBegun openBelowContingent
  unboundedOfSpaced)
open TruthCore.Results.Causality.GrimReaperPatchwork (pivotOne pivotPopulated)

/-- Independence, nonvacuity and sense controls. -/
theorem controls : Certificate := by
  sorry

end TruthCore.Results.Causality.MetricBeginningArrival
