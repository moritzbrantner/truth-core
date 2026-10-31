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
  sorry

end TruthCore.Results.Explanation.NecessaryUltimateSource
