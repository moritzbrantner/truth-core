import TruthCore.Explanation.AnselmCommonSourceAudit
import TruthCore.Results.Explanation.AnselmUltimateSource.Solution

namespace TruthCore.Results.Explanation.AnselmCommonSourceAudit
open TruthCore.Explanation.AnselmUltimateSource
open TruthCore.Explanation.AnselmCommonSourceAudit
open TruthCore.Explanation.WellFoundedSource (PopulatedAt)

/-- Forget power labels using the separate source-to-through interface. -/
theorem forgetPower {W B : Type} (m : Context W B) (w : W)
    (hShared : SharedSelfPowerAt m w) (hPower : PowerGivesThroughAt m w) :
    CommonSelfThroughAt m w := by
  sorry

/-- Under the explicit GLOBAL existence/availability background, the structural
consequence of shared power has exactly unique-source strength. Equivalence is
not evidence of circular reasoning or a defense of either side's truth. -/
theorem characterization {W B : Type} (m : Context W B) (w : W)
    (hPopulation : PopulatedAt m.reality w) (hCoverage : CoverageAt m w)
    (hActual : SourcesActualAt m w) (hUltimate : UltimateAvailableAt m w) :
    CommonSelfThroughCharacterizationAt m w := by
  sorry

end TruthCore.Results.Explanation.AnselmCommonSourceAudit
