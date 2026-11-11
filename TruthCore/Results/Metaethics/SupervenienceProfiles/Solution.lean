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
  constructor
  · refine ⟨weakOnly, ?_, ?_⟩
    · intro w x y _
      rfl
    · intro h
      have hbad := h false true false false rfl
      cases hbad
  constructor
  · refine ⟨competentOnly, ?_, ?_⟩
    · intro w _ x y _
      rfl
    · intro h
      have hbad := h false false true rfl
      cases hbad
  · refine ⟨firstStrong, secondStrong, rfl, ?_, ?_, ⟨false, false, ?_⟩⟩
    · intro w v x y h
      exact h
    · intro w v x y h
      exact congrArg (fun b : Bool => !b) h
    · decide

end TruthCore.Results.Metaethics.SupervenienceProfiles
