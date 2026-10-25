import TruthCore.Modern.Russell.Existence
namespace TruthCore.Results.Modern.Russell.Description
open TruthCore.Modern.Russell.Existence
theorem checks : DescriptionLaw := by
  intro E F
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨⟨c, (hc c).mpr rfl⟩, ?_⟩
    intro x y hx hy
    exact ((hc x).mp hx).trans ((hc y).mp hy).symm
  · rintro ⟨⟨c, hc⟩, hu⟩
    refine ⟨c, fun x => ⟨fun hx => hu x c hx hc, ?_⟩⟩
    intro he
    cases he
    exact hc
end TruthCore.Results.Modern.Russell.Description
