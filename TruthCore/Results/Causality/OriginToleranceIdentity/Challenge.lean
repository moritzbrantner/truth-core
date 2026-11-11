import TruthCore.Causality.OriginToleranceIdentity

namespace TruthCore.Results.Causality.OriginToleranceIdentity
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Causality.ToleranceOriginRival (ToleranceNonEuclideanAt)
open TruthCore.Causality.ToleranceOriginRival.Control (Origin tolerance)
open TruthCore.Causality.OriginToleranceIdentity
open TruthCore.Causality.OriginToleranceIdentity.Control

/-- Bridge: origin closeness that is a tolerance, access determined by origin
closeness, and one individual varied beyond tolerance across two successors of
`w` give the structural tolerance rival at `w`. -/
theorem originToleranceNonEuclidean {W B O : Type} (m : Ontic W B) (Concrete : B → Prop)
    (I : OriginInterface W B O) (w : W)
    (hNear : NearIsTolerance I) (hAccess : OriginDeterminesAccess m I)
    (hVaried : VariedOriginAt m Concrete I w) :
    ToleranceNonEuclideanAt m.frame w := by
  sorry

/-- The faithful origin-tolerance countermodel and the restored surrogate, by
case analysis. -/
theorem faithfulControls : Control.Certificate := by
  sorry

end TruthCore.Results.Causality.OriginToleranceIdentity
