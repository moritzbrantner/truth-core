import TruthCore.Causality.ContingentAncestry
import TruthCore.Models.ContingentAncestry

namespace TruthCore.Results.Causality.ContingentAncestry
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryRootFork
open TruthCore.Causality.CogitoNecessaryConcrete
open TruthCore.Causality.SelectedAncestry
open TruthCore.Causality.ContingentAncestry
open TruthCore.Explanation.ExistencePSR (ExistenceFact)
open TruthCore.Explanation.PSRStrength
open TruthCore.Explanation.ExplanatoryAdequacy
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt ContingentAt)
open TruthCore.Logic (ExcludedMiddle)

/-- Bare necessary existence requires founded descent only among contingent
ancestors. Do not strengthen this to a root/underivedness conclusion. -/
theorem necessaryAncestor {W B : Type} (m : Profile W B) (w : W) (selected : B)
    (hActual : ActualConcrete m w selected)
    (hFounded : ContingentConeFounded m w selected)
    (hDep : ConeContingentGrounded m w selected)
    (hEM : ExcludedMiddle) : NecessaryAncestor m w selected := by
  sorry

theorem necessaryConcrete {W B : Type} (m : Profile W B) (w : W) (selected : B)
    (hActual : ActualConcrete m w selected)
    (hFounded : ContingentConeFounded m w selected)
    (hDep : ConeContingentGrounded m w selected)
    (hEM : ExcludedMiddle) : NecessaryConcreteAt m w := by
  sorry

theorem foundationComparison : FoundationComparison := by
  sorry

/-- Strict weakening and the boundary of the new conclusion. -/
theorem strictness : TruthCore.Models.ContingentAncestry.Strictness := by
  sorry

/-- Expose the strengthening relation as a typed corpus edge. -/
theorem contingentFoundationOfFull {W B : Type} (m : Profile W B) (w : W) (selected : B)
    (hWF : ConeWellFounded m w selected) : ContingentConeFounded m w selected := by
  sorry

end TruthCore.Results.Causality.ContingentAncestry
