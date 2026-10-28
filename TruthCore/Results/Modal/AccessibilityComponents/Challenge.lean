import TruthCore.Modal.AccessibilityComponents

namespace TruthCore.Results.Modal.AccessibilityComponents
open TruthCore.Modal
universe u

/-- SCCs are exactly accessibility equivalence classes; weak connectivity alone
cannot identify them. Nil paths are included, hence reflexivity is explicit. -/
theorem certificate : TruthCore.Modal.AccessibilityComponents.Certificate.{u} := by
  sorry

end TruthCore.Results.Modal.AccessibilityComponents
