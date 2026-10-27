import TruthCore.Causality.NecessarilyUnderived

namespace TruthCore.Results.Causality.NecessarilyUnderived.LiftFromBridges

open TruthCore.Causality.NecessarilyUnderived
open TruthCore.German.Kant.CosmologicalInference

/-- Separate cross-world support restrictions factor through the precise
necessary-predecessor lifting proposition. -/
theorem checks {World Being : Type} (m : Ontic World Being)
    (supportsEsse : World → Being → Being → Prop) (w₀ : World)
    (h0 : ActualReflexive m w₀)
    (h1 : NoContingentGroundOfNecessary m supportsEsse w₀)
    (h2 : NoNovelNecessarySupport m supportsEsse w₀) :
    NecessaryPredecessorLifting m supportsEsse w₀ := by
  sorry

end TruthCore.Results.Causality.NecessarilyUnderived.LiftFromBridges
