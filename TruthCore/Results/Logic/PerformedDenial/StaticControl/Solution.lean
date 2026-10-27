import TruthCore.Logic.PerformedDenial

namespace TruthCore.Results.Logic.PerformedDenial.StaticControl
open TruthCore.Logic.PerformedDenial

/-- Countermodel to occurrence implying succession. -/
theorem staticControl : StaticEpisodeControl := by
  refine ⟨fun _ => True, fun _ => false, trivial, ?_⟩
  intro ⟨t₁, t₂, hDiff⟩
  cases t₁
  cases t₂
  exact hDiff rfl

end TruthCore.Results.Logic.PerformedDenial.StaticControl
