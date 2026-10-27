import TruthCore.Causality.NecessarilyUnderived

namespace TruthCore.Results.Causality.NecessarilyUnderived.NonRefutationLift

open TruthCore.Causality.NecessarilyUnderived
open TruthCore.German.Kant.CosmologicalInference

/-- Constructive non-transcription proof: use well-founded induction and
transport each hypothesized supporter into an actual necessary predecessor. -/
theorem checks {World Being : Type} (m : Ontic World Being)
    (supportsEsse : World → Being → Being → Prop) (w₀ : World)
    (h0 : NecessaryBeing m w₀)
    (h1 : WellFoundedPresentEsseSupport m supportsEsse w₀)
    (h2 : NecessaryPredecessorLifting m supportsEsse w₀) :
    NonRefutableNecessarilyUnderived m supportsEsse w₀ := by
  exact not_not_underived_of_lifting m supportsEsse w₀ h0 h1 h2

end TruthCore.Results.Causality.NecessarilyUnderived.NonRefutationLift
