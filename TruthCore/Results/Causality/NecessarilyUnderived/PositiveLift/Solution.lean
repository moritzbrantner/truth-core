import TruthCore.Causality.NecessarilyUnderived

namespace TruthCore.Results.Causality.NecessarilyUnderived.PositiveLift

open TruthCore.Causality.NecessarilyUnderived
open TruthCore.German.Kant.CosmologicalInference

/-- The constructive lifting theorem plus explicit excluded middle yields
one actual rigid necessary individual without any existing incoming support. -/
theorem checks {World Being : Type} (m : Ontic World Being)
    (supportsEsse : World → Being → Being → Prop) (w₀ : World)
    (h0 : NecessaryBeing m w₀)
    (h1 : WellFoundedPresentEsseSupport m supportsEsse w₀)
    (h2 : NecessaryPredecessorLifting m supportsEsse w₀)
    (h3 : TruthCore.Logic.ExcludedMiddle) :
    NecessarilyUnderived m supportsEsse w₀ := by
  exact underived_of_lifting_and_excludedMiddle m supportsEsse w₀ h0 h1 h2 h3

end TruthCore.Results.Causality.NecessarilyUnderived.PositiveLift
