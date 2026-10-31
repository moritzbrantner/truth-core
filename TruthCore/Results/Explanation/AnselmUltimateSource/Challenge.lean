import TruthCore.Explanation.AnselmUltimateSource

namespace TruthCore.Results.Explanation.AnselmUltimateSource
open TruthCore.Explanation.AnselmUltimateSource
open TruthCore.Explanation.WellFoundedSource

/-- Direct uniqueness needs only coverage and the two self-power interfaces. -/
theorem atMostOne {W B : Type} (m : Context W B) (w : W)
    (hCoverage : CoverageAt m w) (hShared : SharedSelfPowerAt m w)
    (hPower : PowerGivesThroughAt m w) : AtMostOneUltimateSourceAt m w := by
  sorry

/-- Existence retains actual population and ultimate availability explicitly. -/
theorem existsSource {W B : Type} (m : Context W B) (w : W)
    (hPopulation : PopulatedAt m.reality w) (hCoverage : CoverageAt m w)
    (hActual : SourcesActualAt m w) (hUltimate : UltimateAvailableAt m w) :
    SomeUltimateSourceAt m w := by
  sorry

/-- Compose the two derivations, not a new universal God or necessity claim. -/
theorem uniqueSource {W B : Type} (m : Context W B) (w : W)
    (hPopulation : PopulatedAt m.reality w) (hCoverage : CoverageAt m w)
    (hActual : SourcesActualAt m w) (hUltimate : UltimateAvailableAt m w)
    (hShared : SharedSelfPowerAt m w) (hPower : PowerGivesThroughAt m w) :
    UniqueUltimateSourceAt m w := by
  sorry


/-- Pointwise ultimate availability plus uniqueness yields one SAME universal
ultimate source, avoiding an unsupported exchange of existential quantifiers. -/
theorem uniqueUniversalSource {W B : Type} (m : Context W B) (w : W)
    (hPopulation : PopulatedAt m.reality w) (hCoverage : CoverageAt m w)
    (hActual : SourcesActualAt m w) (hUltimate : UltimateAvailableAt m w)
    (hShared : SharedSelfPowerAt m w) (hPower : PowerGivesThroughAt m w) :
    UniqueUniversalUltimateSourceAt m w := by
  sorry

end TruthCore.Results.Explanation.AnselmUltimateSource
