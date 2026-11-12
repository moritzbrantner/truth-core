import TruthCore.Causality.NecessarySupportActualScope
import TruthCore.Results.Causality.NecessarySupportCoverage.Solution
import TruthCore.Results.Causality.ActualUnderivedEssenceEsse.Solution

namespace TruthCore.Results.Causality.NecessarySupportActualScope

open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryRootFork
open TruthCore.Causality.NecessarilyUnderived
open TruthCore.Causality.NecessaryConcreteUnderived
open TruthCore.Causality.NecessarySupportCoverage
open TruthCore.Causality.NecessarySupportActualScope
open TruthCore.Causality.NecessarySupportActualScope.Control
open TruthCore.Causality.NecessarySupportCoverage.Control (Tri)
open TruthCore.Causality.ActualUnderivedEssenceEsse (ActualNecessaryWellFounded)
open TruthCore.German.Kant.CosmologicalInference (Ontic NecessaryAt ContingentAt NecessaryBeing)
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)

/-- J1 gives its selected-world instance: take the arbitrary world of J1 to be `w`. -/
theorem actualOfNoContingent (m : Profile W B) (w : W)
    (hNoCont : NoContingentConcreteSupport m w) :
    ActualNoContingentConcreteSupport m w := by
  sorry

/-- The join's endpoint from a necessary concretum, well-founded actual grounding,
J1 at the selected world only, coverage and excluded middle. Composes the existing
`ActualUnderivedEssenceEsse.actual_source_not_not` on the concrete subtype (an
actually existing necessary concretum with no concrete supporter existing at `w`,
double-negated) with the existing `NecessarySupportCoverage.presentSupportWF`;
coverage then excludes a concrete supporter existing at any admitted world. -/
theorem underivedFromNecessityOfActualCoverage (m : Profile W B) (w : W)
    (hNecessary : NecessaryConcreteAt m w) (hWF : ActualGroundingWF m w)
    (hAct : ActualNoContingentConcreteSupport m w)
    (hCov : NecessarySupportActuallyCovered m w) (hEM : ExcludedMiddle) :
    NecessaryConcreteUnderivedAt m w := by
  sorry

/-! ## Controls -/

/-- Both controls hold. -/
theorem controls : Controls := by
  sorry

end TruthCore.Results.Causality.NecessarySupportActualScope
