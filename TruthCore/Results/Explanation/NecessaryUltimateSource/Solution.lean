import TruthCore.Explanation.NecessaryUltimateSource
import TruthCore.Results.Causality.SelectedAncestry.Solution
import TruthCore.Results.Explanation.AnselmUltimateSource.Solution

namespace TruthCore.Results.Explanation.NecessaryUltimateSource
open TruthCore.Explanation.AnselmUltimateSource
open TruthCore.Explanation.NecessaryUltimateSource
open TruthCore.Causality.SelectedAncestry
open TruthCore.Causality.NecessaryRootFork
open TruthCore.Logic (ExcludedMiddle)

/-- Same-witness composition. Local foundation/dependence apply to the explicit
 distinct-through profile. No global ultimate availability is assumed. -/
theorem necessaryUniqueSource {W B : Type} (m : Context W B)
    (concrete : B → Prop) (w : W) (selected : B)
    (hActual : ActualConcrete (distinctGroundProfile m concrete) w selected)
    (hWF : ConeWellFounded (distinctGroundProfile m concrete) w selected)
    (hDep : ConeContingentGrounded (distinctGroundProfile m concrete) w selected)
    (hEM : ExcludedMiddle)
    (hCoverage : CoverageAt m w) (hActualSources : SourcesActualAt m w)
    (hConcreteSources : ConcreteSourcesAt m concrete w)
    (hShared : SharedSelfPowerAt m w) (hPower : PowerGivesThroughAt m w) :
    NecessaryUniqueUltimateSourceAt m w := by
  obtain ⟨x, hCone, hNecessary, hRoot⟩ :=
    TruthCore.Results.Causality.SelectedAncestry.necessaryRootAncestor
      (distinctGroundProfile m concrete) w selected hActual hWF hDep hEM
  have hNoDistinct : ∀ y, m.through w x y → y = x := by
    intro y hThrough
    rcases hEM (y = x) with hEq | hNe
    · exact hEq
    · exact False.elim (hRoot y
        ⟨hConcreteSources x hCone.1.1 hCone.1.2 y hThrough,
          hActualSources x y hThrough, hThrough, hNe⟩)
  obtain ⟨y, hThrough⟩ := hCoverage x hCone.1.2
  have hSelf : m.through w x x := (hNoDistinct y hThrough) ▸ hThrough
  have hUltimate : UltimateSourceAt m w x :=
    ⟨hCone.1.2, x, hSelf, hNoDistinct⟩
  refine ⟨x, hNecessary, hUltimate, ?_⟩
  intro z hz
  exact TruthCore.Results.Explanation.AnselmUltimateSource.atMostOne
    m w hCoverage hShared hPower z x hz hUltimate

end TruthCore.Results.Explanation.NecessaryUltimateSource
