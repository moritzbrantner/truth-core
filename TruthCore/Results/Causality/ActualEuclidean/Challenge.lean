import TruthCore.Causality.ActualEuclidean
import TruthCore.Results.Causality.InertEmptiness.Solution
import TruthCore.Results.Causality.LocalFramePossibleExternalCause.Solution

namespace TruthCore.Results.Causality.ActualEuclidean
open TruthCore.Causality.ActualEuclidean
open TruthCore.Causality.InertEmptiness (EmptinessStaysEmpty PossiblyContingentsAbsentThenPresent)
open TruthCore.Causality.SpineRivalsStageOne.Control (Place)
open TruthCore.Causality.BruteFoundationBoundary (NecessaryConcreteAt)
open TruthCore.Causality.CountTemporalNecessity (HistoryPresenceActual)
open TruthCore.Causality.NecessarilyUnderived (ActualReflexive)
open TruthCore.Causality.PossibleCauseOfContingency
  (Scenario PossiblyBeginsAt CausalOpportunityAt)
open TruthCore.Modal (Euclidean)
open TruthCore.Modal.TemporalHistory (History)

/-- Strength order: global Euclidean access gives Euclidean access at any world. -/
theorem euclideanAtOfEuclidean {W : Type} (frame : TruthCore.Modal.Frame W) (w : W)
    (hEuclidean : Euclidean frame) : EuclideanAt frame w := by
  sorry

/-- The inert-emptiness arrival with Euclidean access required only at the
selected world. Reuses `earlierNecessary` for the accessible history. -/
theorem inertNecessaryConcrete {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) (G : W → B → B → Prop) (w : W)
    (hEuclidean : EuclideanAt h.ontic.frame w)
    (hReflexive : ActualReflexive h.ontic w)
    (hPresence : HistoryPresenceActual h)
    (hInert : EmptinessStaysEmpty h Concrete)
    (hPossible : PossiblyContingentsAbsentThenPresent h Concrete w) :
    NecessaryConcreteAt ⟨h.ontic, Concrete, G⟩ w := by
  sorry

/-- The possible-external-cause arrival with Euclidean access required only at
the selected world. Reuses `necessaryOfExternalCandidate` for the same cause. -/
theorem externalNecessaryConcrete {W B : Type} (s : Scenario W B) (w : W)
    (hEuclidean : EuclideanAt s.ontic.frame w)
    (hReflexive : ActualReflexive s.ontic w)
    (hBeginning : PossiblyBeginsAt s w)
    (hOpportunity : CausalOpportunityAt s w) :
    TruthCore.Causality.PossibleCauseOfContingency.NecessaryConcreteAt s w := by
  sorry

/-- The separating model and the stepwise status, by case analysis. -/
theorem controls : Control.Certificate := by
  sorry

end TruthCore.Results.Causality.ActualEuclidean
