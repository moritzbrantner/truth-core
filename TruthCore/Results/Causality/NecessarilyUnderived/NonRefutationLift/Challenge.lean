import TruthCore.Causality.NecessarilyUnderived

namespace TruthCore.Results.Causality.NecessarilyUnderived.NonRefutationLift

open TruthCore.Causality.NecessarilyUnderived
open TruthCore.German.Kant.CosmologicalInference

/-- Nonempty necessary population, well-founded actual dependency and
necessary-predecessor lifting refute denying a rigidly underived bearer. -/
theorem checks {World Being : Type} (m : Ontic World Being)
    (supportsEsse : World → Being → Being → Prop) (w₀ : World)
    (h0 : NecessaryBeing m w₀)
    (h1 : WellFoundedPresentEsseSupport m supportsEsse w₀)
    (h2 : NecessaryPredecessorLifting m supportsEsse w₀) :
    NonRefutableNecessarilyUnderived m supportsEsse w₀ := by
  sorry

end TruthCore.Results.Causality.NecessarilyUnderived.NonRefutationLift
