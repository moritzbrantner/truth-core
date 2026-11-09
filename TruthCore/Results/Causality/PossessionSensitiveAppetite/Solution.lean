module
public import TruthCore.Causality.PossessionSensitiveAppetite
@[expose] public section
namespace TruthCore.Results.Causality.PossessionSensitiveAppetite
open TruthCore.Causality.PossessionSensitiveAppetite

theorem capacity (m : Profile) (hc : Calibration m) (ha : Availability m) : Capacity m := by
  intro p hp
  cases p with
  | false => exact ⟨.acquire, ha false hp, hc false hp, Or.inl ⟨rfl, rfl⟩, rfl⟩
  | true => exact ⟨.retain, ha true hp, hc true hp, Or.inr ⟨rfl, rfl⟩, rfl⟩

theorem controls : Controls := by
  have hc : Calibration responsive := by
    intro p _; cases p <;> decide
  have ha : Availability responsive := by
    intro p _; exact True.intro
  have hn : ¬ Calibration cognitiveOnly := by
    intro h
    exact Nat.lt_irrefl 0 (h false True.intro)
  have hnc : ¬ Capacity cognitiveOnly := by
    intro h
    obtain ⟨a, _, hr, _, _⟩ := h false True.intro
    exact Nat.lt_irrefl 0 hr
  have hna : ¬ Availability unavailable := by
    intro h
    exact h false True.intro
  have hnu : ¬ Capacity unavailable := by
    intro h
    obtain ⟨a, hav, _, _, _⟩ := h false True.intro
    exact hav
  exact ⟨⟨(fun _ => True.intro), hc, ha, capacity responsive hc ha⟩,
    ⟨(fun _ => True.intro), ha, hn, hnc⟩,
    ⟨(fun _ => True.intro), hc, hna, hnu⟩⟩
end TruthCore.Results.Causality.PossessionSensitiveAppetite
