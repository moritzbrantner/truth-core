import Mathlib.Order.WellFounded
import TruthCore.Results.Causality.RegressAccessibilityExcludesSeries.Solution

namespace TruthCore.Results.Causality.RegressReadingsCoincide
open TruthCore.Causality

/-- The forward direction reuses the constructive result
`REGRESS-ACCESSIBILITY-EXCLUDES-DESCENDING-SERIES`. The converse is Mathlib's
`acc_iff_isEmpty_descending_chain`, whose proof uses classical choice: from a
being that is not accessible it builds an infinite descending series. -/
theorem regressReadingsCoincideClassically :
    RegressReadingsCoincideClassically := by
  intro Being CausesAsCaused
  refine ⟨RegressAccessibilityExcludesSeries.accessibilityReadingExcludesDescendingSeries
      Being CausesAsCaused, ?_⟩
  intro hNoSeries x
  refine acc_iff_isEmpty_descending_chain.mpr ⟨fun ⟨series, _, hSeries⟩ => ?_⟩
  exact hNoSeries ⟨series, hSeries⟩

end TruthCore.Results.Causality.RegressReadingsCoincide
