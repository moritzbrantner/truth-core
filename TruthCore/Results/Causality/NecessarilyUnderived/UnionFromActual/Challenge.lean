import TruthCore.Causality.NecessarilyUnderived

namespace TruthCore.Results.Causality.NecessarilyUnderived.UnionFromActual

open TruthCore.Causality.NecessarilyUnderived
open TruthCore.German.Kant.CosmologicalInference

/-- A world-invariant *inclusion* of necessary incoming edges and actual
well-foundedness imply global union well-foundedness. Converse fails. -/
theorem checks {World Being : Type} (m : Ontic World Being)
    (supportsEsse : World → Being → Being → Prop) (w₀ : World)
    (h0 : ActualReflexive m w₀)
    (h1 : NoNovelNecessarySupport m supportsEsse w₀)
    (h2 : WellFoundedPresentEsseSupport m supportsEsse w₀) :
    WellFoundedUnionNecessarySupport m supportsEsse w₀ := by
  sorry

end TruthCore.Results.Causality.NecessarilyUnderived.UnionFromActual
