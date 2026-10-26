import TruthCore.Causality.GroundingRegress

namespace TruthCore.Results.Causality.GroundingYieldsRegress
open TruthCore.Causality TruthCore.Causality.GroundingRegress

/-- Induction on each being's grounding certificate. An intrinsic source has
no per se cause, so it is accessible outright. A being that borrows from `y`
has `y` as its only immediate per se cause, and `y` is accessible by the
induction hypothesis. No classical logic and no axiom is used. -/
theorem groundingWithUniqueCauseYieldsRegressReading :
    GroundingWithUniqueCauseYieldsRegressReading := by
  intro Being causesAsCaused intrinsic hGrounded hSources hUnique x
  induction hGrounded x with
  | intrinsic x hSource =>
    exact ⟨x, fun y hy => absurd hy (hSources x hSource y)⟩
  | borrowed hLink _ ih =>
    exact ⟨_, fun z hz => hUnique _ _ _ hLink hz ▸ ih⟩

end TruthCore.Results.Causality.GroundingYieldsRegress
