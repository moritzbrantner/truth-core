import TruthCore.Causality.ToleranceOriginRival
import TruthCore.Causality.SpineRivalsStageOne

namespace TruthCore.Results.Causality.ToleranceOriginRival
open TruthCore.Causality.ToleranceOriginRival
open TruthCore.Causality.ToleranceOriginRival.Control
open TruthCore.Causality.SpineRivalsStageOne (ReflexiveNonEuclidean)

/-- Strength order: the tolerance rival at any world gives the stepwise rival's
global statement on the same frame. -/
theorem toleranceReflexiveNonEuclidean {W : Type} (frame : TruthCore.Modal.Frame W) (w : W)
    (hTolerance : ToleranceNonEuclideanAt frame w) : ReflexiveNonEuclidean frame := by
  sorry

/-- The tolerance omission model and its closure reading, by case analysis. -/
theorem controls : Control.Certificate := by
  sorry

end TruthCore.Results.Causality.ToleranceOriginRival
