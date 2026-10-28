import TruthCore.Modal.ExistenceDegrees
import TruthCore.Results.Modal.ExistenceDegrees.Solution

namespace TruthCore.Results.Modal.ExistenceDegreesActual
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Causality.NecessarilyUnderived (ActualReflexive)
open TruthCore.Modal.ExistenceDegrees

/-- Source-fidelity adapter: the actual-presence-guarded invariance conditional
suffices under the same explicit actual reflexivity and necessity premises.
It composes the existing analyst-profile theorem without changing its frozen
type. This is no new philosophical discovery, no value bridge and no extension
from the root-accessible family to all metaphysical worlds. -/
theorem globalMaximumFromActualInvariant {World Being Degree : Type} [Preorder Degree]
    (m : Ontic World Being) (intensity : World → Being → Degree)
    (w₀ : World) (n : Being)
    (hActual : ActualReflexive m w₀)
    (hNecessary : NecessaryAt m w₀ n)
    (hPotential : OtherDirectedPotentialCause m w₀ n)
    (hBound : WeakCauseDegreeBound m intensity w₀)
    (hInvariant : ActualNecessaryDegreeInvariant m intensity w₀ n)
    (hEM : TruthCore.Logic.ExcludedMiddle) :
    NecessaryGlobalDegreeMaximum m intensity w₀ n := by
  apply TruthCore.Results.Modal.ExistenceDegrees.necessaryGlobalMaximum
    m intensity w₀ n hActual hNecessary hPotential hBound
  · intro hn
    exact hInvariant ⟨hn w₀ hActual, hn⟩
  · exact hEM

end TruthCore.Results.Modal.ExistenceDegreesActual
