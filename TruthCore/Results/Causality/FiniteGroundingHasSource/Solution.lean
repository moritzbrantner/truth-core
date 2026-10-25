import TruthCore.Causality.EssentialPower

namespace TruthCore.Results.Causality.FiniteGroundingHasSource
open TruthCore.Causality

/-- Induction on an actual grounding derivation extracts the independent
source at its base and a finite causal path back to it. No assumption of
causal well-foundedness, no classical logic and no new axiom are used. -/
theorem finiteGroundingHasSource : FiniteGroundingHasSource := by
  intro Being causesAsCaused intrinsic x grounded
  induction grounded with
  | intrinsic x hSource =>
    exact ⟨x, .same x, hSource⟩
  | borrowed hLink _ ih =>
    obtain ⟨source, path, hSource⟩ := ih
    exact ⟨source, .link hLink path, hSource⟩

end TruthCore.Results.Causality.FiniteGroundingHasSource
