module

public import TruthCore.Metaethics.SupervenienceProfiles

@[expose] public section

namespace TruthCore.Results.Metaethics.SupervenienceProfiles

open TruthCore.Metaethics.SupervenienceProfiles

theorem strongImpliesWeak {World Case : Type} (p : Profile World Case)
    (h : Strong p) : Weak p := by
  intro w x y hNatural
  exact h w w x y hNatural

theorem controls : Controls := by
  refine ⟨⟨weakOnly, by decide, by decide⟩,
    ⟨competentOnly, by decide, by decide⟩,
    ⟨firstStrong, secondStrong, rfl, by decide, by decide, ?_⟩⟩
  exact ⟨false, false, by decide⟩

end TruthCore.Results.Metaethics.SupervenienceProfiles
