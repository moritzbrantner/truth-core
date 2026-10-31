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
  rcases rootForkOfAccessibility m w selected hActual
      (accessibleOfConeWellFounded m w selected hActual hWF) hEM with
      hNecessary | ⟨x, hCone, hContingent, hRoot⟩
  · exact hNecessary
  · obtain ⟨source, hSource⟩ := hDep x hCone hContingent
    exact False.elim (hRoot source hSource)

theorem necessaryConcrete {W B : Type} (m : Profile W B) (w : W) (selected : B)
    (hActual : ActualConcrete m w selected)
    (hWF : ConeWellFounded m w selected)
    (hDep : ConeContingentGrounded m w selected)
    (hEM : ExcludedMiddle) : NecessaryConcreteAt m w := by
  obtain ⟨ancestor, hCone, hNecessary, _⟩ :=
    necessaryRootAncestor m w selected hActual hWF hDep hEM
  exact ⟨ancestor, hCone.1.1, hCone.1.2, hNecessary⟩

theorem controls : TruthCore.Models.SelectedAncestry.Controls := by
  exact TruthCore.Models.SelectedAncestry.controls

/-- Restrict the two existing global premises to any selected cone. -/
theorem scopeComparison : ScopeComparison := by
  intro W B m w selected
  constructor
  · intro hWF
    exact InvImage.wf
      (fun x : {x // Cone m w selected x} =>
        (⟨x.val, x.property.1⟩ : {x // ActualConcrete m w x})) hWF
  · intro hDep x hCone hContingent
    exact hDep x hCone.1.1 hCone.1.2 hContingent

end TruthCore.Results.Causality.SelectedAncestry
