import TruthCore.Causality.NecessarilyUnderived

namespace TruthCore.Results.Causality.NecessarilyUnderived.PositiveUnion

open TruthCore.Causality.NecessarilyUnderived
open TruthCore.German.Kant.CosmologicalInference

/-- Alternative world-varying dependency route: well-foundedness of the
union graph on necessary bearers replaces cross-world edge invariance. -/
theorem checks {World Being : Type} (m : Ontic World Being)
    (supportsEsse : World → Being → Being → Prop) (w₀ : World)
    (h0 : NecessaryBeing m w₀)
    (h1 : ActualReflexive m w₀)
    (h2 : NoContingentGroundOfNecessary m supportsEsse w₀)
    (h3 : WellFoundedUnionNecessarySupport m supportsEsse w₀)
    (h4 : TruthCore.Logic.ExcludedMiddle) :
    NecessarilyUnderived m supportsEsse w₀ := by
  sorry

end TruthCore.Results.Causality.NecessarilyUnderived.PositiveUnion
