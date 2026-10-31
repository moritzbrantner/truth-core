import TruthCore.Causality.SelectedAncestry
import TruthCore.Models.SelectedAncestry

namespace TruthCore.Results.Causality.SelectedAncestry
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryRootFork
open TruthCore.Causality.SelectedAncestry
open TruthCore.Logic (ExcludedMiddle)

/-- One full actual cone suffices; unrelated concreta are unconstrained. -/
theorem necessaryRootAncestor {W B : Type} (m : Profile W B) (w : W) (selected : B)
    (hActual : ActualConcrete m w selected)
    (hWF : ConeWellFounded m w selected)
    (hDep : ConeContingentGrounded m w selected)
    (hEM : ExcludedMiddle) : NecessaryRootAncestor m w selected := by
  sorry

/-- Project the same selected-root witness to the shared concrete conclusion. -/
theorem necessaryConcrete {W B : Type} (m : Profile W B) (w : W) (selected : B)
    (hActual : ActualConcrete m w selected)
    (hWF : ConeWellFounded m w selected)
    (hDep : ConeContingentGrounded m w selected)
    (hEM : ExcludedMiddle) : NecessaryConcreteAt m w := by
  sorry

/-- Same-profile omissions and one combined strict scope witness. -/
theorem controls : TruthCore.Models.SelectedAncestry.Controls := by
  sorry

/-- Restrict the two existing global premises to any selected cone. -/
theorem scopeComparison : ScopeComparison := by
  sorry

end TruthCore.Results.Causality.SelectedAncestry
