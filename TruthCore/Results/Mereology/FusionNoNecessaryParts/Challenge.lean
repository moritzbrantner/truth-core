import TruthCore.Mereology.FusionNoNecessaryParts

namespace TruthCore.Results.Mereology.FusionNoNecessaryParts
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Mereology.UniversalFusionBoundary
open TruthCore.Mereology.FusionNoNecessaryParts

/-- A selected Sum2 fusion of members without necessary parts has no necessary
parts under explicit downward closure. No sum's actuality is inferred. -/
theorem noNecessaryParts {W B : Type} [PartialOrder B]
    (m : Ontic W B) (w : W) (family : Set B) (sum : B)
    (hFusion : Fusion family sum)
    (hFamily : FamilyNoNecessaryPartsAt m w family)
    (hDownward : NecessityDownwardAlongParthoodAt m w) :
    NoNecessaryPartsAt m w sum := by
  sorry

end TruthCore.Results.Mereology.FusionNoNecessaryParts
