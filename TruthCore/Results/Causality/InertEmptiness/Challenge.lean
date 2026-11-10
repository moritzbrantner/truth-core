import TruthCore.Causality.InertEmptiness

namespace TruthCore.Results.Causality.InertEmptiness
open TruthCore.Causality.InertEmptiness
open TruthCore.Causality.BruteFoundationBoundary (NecessaryConcreteAt)
open TruthCore.Causality.CountTemporalNecessity (HistoryPresenceActual)
open TruthCore.Causality.NecessarilyUnderived (ActualReflexive)
open TruthCore.German.Kant.CosmologicalInference (ContingentAt NecessaryAt)
open TruthCore.Modal (Euclidean)
open TruthCore.Modal.TemporalHistory (History)

/-- Stage one of the modal spine without a causal premise. If a history with a
contingent-free moment before a contingent-populated one is accessible, then
under inert emptiness, presence-to-existence and the two frame conditions one
and the same concrete individual exists at `w` and at every world accessible
from `w`. `G` is any grounding relation: the conclusion does not constrain it. -/
theorem necessaryConcrete {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) (G : W → B → B → Prop) (w : W)
    (hEuclidean : Euclidean h.ontic.frame)
    (hReflexive : ActualReflexive h.ontic w)
    (hPresence : HistoryPresenceActual h)
    (hInert : EmptinessStaysEmpty h Concrete)
    (hPossible : PossiblyContingentsAbsentThenPresent h Concrete w) :
    NecessaryConcreteAt ⟨h.ontic, Concrete, G⟩ w := by
  sorry

/-- Omission and nonvacuity controls on four two-world interpretations with natural-number times. -/
theorem controls : Control.Certificate := by
  sorry

end TruthCore.Results.Causality.InertEmptiness
