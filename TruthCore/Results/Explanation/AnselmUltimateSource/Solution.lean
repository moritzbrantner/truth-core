import TruthCore.Explanation.AnselmUltimateSource

namespace TruthCore.Results.Explanation.AnselmUltimateSource
open TruthCore.Explanation.AnselmUltimateSource
open TruthCore.Explanation.WellFoundedSource

/-- Direct uniqueness needs only coverage and the two self-power interfaces. -/
theorem atMostOne {W B : Type} (m : Context W B) (w : W)
    (hCoverage : CoverageAt m w) (hShared : SharedSelfPowerAt m w)
    (hPower : PowerGivesThroughAt m w) : AtMostOneUltimateSourceAt m w := by
  intro x y hx hy
  rcases hx with ⟨hxActual, tx, _, hxRoot⟩
  rcases hy with ⟨hyActual, ty, _, hyRoot⟩
  obtain ⟨sx, hsx⟩ := hCoverage x hxActual
  obtain ⟨sy, hsy⟩ := hCoverage y hyActual
  have hxSelf : m.through w x x := (hxRoot sx hsx) ▸ hsx
  have hySelf : m.through w y y := (hyRoot sy hsy) ▸ hsy
  obtain ⟨c, hCommon⟩ := hShared
  have hcX : c = x := hxRoot c (hPower x c (hCommon x hxSelf))
  have hcY : c = y := hyRoot c (hPower y c (hCommon y hySelf))
  exact hcX.symm.trans hcY

/-- Existence retains actual population and ultimate availability explicitly. -/
theorem existsSource {W B : Type} (m : Context W B) (w : W)
    (hPopulation : PopulatedAt m.reality w) (hCoverage : CoverageAt m w)
    (hActual : SourcesActualAt m w) (hUltimate : UltimateAvailableAt m w) :
    SomeUltimateSourceAt m w := by
  obtain ⟨x, hx⟩ := hPopulation
  obtain ⟨y, hxy⟩ := hCoverage x hx
  obtain ⟨z, hxz⟩ := hUltimate x y hxy
  exact ⟨z, hActual x z hxz.1, x, hxz⟩

/-- Compose the two derivations, not a new universal God or necessity claim. -/
theorem uniqueSource {W B : Type} (m : Context W B) (w : W)
    (hPopulation : PopulatedAt m.reality w) (hCoverage : CoverageAt m w)
    (hActual : SourcesActualAt m w) (hUltimate : UltimateAvailableAt m w)
    (hShared : SharedSelfPowerAt m w) (hPower : PowerGivesThroughAt m w) :
    UniqueUltimateSourceAt m w := by
  obtain ⟨s, hs⟩ := existsSource m w hPopulation hCoverage hActual hUltimate
  refine ⟨s, hs, ?_⟩
  intro t ht
  exact atMostOne m w hCoverage hShared hPower t s ht hs


/-- Pointwise ultimate availability plus uniqueness yields one SAME universal
ultimate source, avoiding an unsupported exchange of existential quantifiers. -/
theorem uniqueUniversalSource {W B : Type} (m : Context W B) (w : W)
    (hPopulation : PopulatedAt m.reality w) (hCoverage : CoverageAt m w)
    (hActual : SourcesActualAt m w) (hUltimate : UltimateAvailableAt m w)
    (hShared : SharedSelfPowerAt m w) (hPower : PowerGivesThroughAt m w) :
    UniqueUniversalUltimateSourceAt m w := by
  obtain ⟨s, hs, hOnly⟩ := uniqueSource m w hPopulation hCoverage hActual hUltimate hShared hPower
  refine ⟨s, ⟨hs.1, ?_⟩, ?_⟩
  · intro x hx
    obtain ⟨y, hxy⟩ := hCoverage x hx
    obtain ⟨z, hxz⟩ := hUltimate x y hxy
    have hz : z = s := hOnly z ⟨hActual x z hxz.1, x, hxz⟩
    exact hz ▸ hxz
  · intro t ht
    obtain ⟨x, hx⟩ := hPopulation
    exact hOnly t ⟨ht.1, x, ht.2 x hx⟩

end TruthCore.Results.Explanation.AnselmUltimateSource
