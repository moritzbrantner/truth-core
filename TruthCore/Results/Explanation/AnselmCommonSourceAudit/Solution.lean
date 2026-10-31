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
  obtain ⟨c, hc⟩ := hShared
  exact ⟨c, fun x hx => hPower x c (hc x hx)⟩

/-- Under the explicit GLOBAL existence/availability background, the structural
consequence of shared power has exactly unique-source strength. Equivalence is
not evidence of circular reasoning or a defense of either side's truth. -/
theorem characterization {W B : Type} (m : Context W B) (w : W)
    (hPopulation : PopulatedAt m.reality w) (hCoverage : CoverageAt m w)
    (hActual : SourcesActualAt m w) (hUltimate : UltimateAvailableAt m w) :
    CommonSelfThroughCharacterizationAt m w := by
  constructor
  · intro hCommon
    -- A proof-only interpretation change: through and the ontology stay
    -- literally unchanged. No facts about the original power relation follow.
    exact TruthCore.Results.Explanation.AnselmUltimateSource.uniqueSource
      {m with selfPowerFrom := m.through} w hPopulation hCoverage hActual
      hUltimate hCommon (fun _ _ h => h)
  · rintro ⟨s, hs, hOnly⟩
    refine ⟨s, ?_⟩
    intro x hx
    obtain ⟨z, hxz⟩ := hUltimate x x hx
    have hz : z = s := hOnly z ⟨hActual x z hxz.1, x, hxz⟩
    exact hz ▸ hxz.1

end TruthCore.Results.Explanation.AnselmCommonSourceAudit
