import TruthCore.Modern.Russell.Existence
namespace TruthCore.Results.Modern.Russell.Projection
open TruthCore.Modern.Russell.Existence
theorem checks (F : Extension) (g : Grounding)
    (hRealized : Realized F) (hBasis : InstanceBasisLaw F g) :
    GroundingProjection F g := by
  obtain ⟨x, hx⟩ := hRealized
  refine ⟨⟨x, hx, hBasis x hx⟩, ?_, ?_, ?_⟩
  · rintro ⟨_, _, h⟩
    exact h
  · intro x hx
    exact Bool.noConfusion hx
  · rintro ⟨x, hx⟩
    exact Bool.noConfusion hx
end TruthCore.Results.Modern.Russell.Projection
