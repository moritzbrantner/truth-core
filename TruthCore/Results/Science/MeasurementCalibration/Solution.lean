import TruthCore.Science.MeasurementCalibration
import Mathlib.Tactic.Abel
namespace TruthCore.Results.Science.MeasurementCalibration
open TruthCore.Science.MeasurementCalibration

/-- Exact identifiability boundary in the stipulated additive profile, with
inhabited omission controls. No actual device/reliability claim follows. -/
theorem certificate : Certificate := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro X V _ f g b c
    constructor
    · intro h
      refine ⟨b - c, ?_, ?_⟩
      · abel
      · intro x
        calc
          g x = (f x + b) - c := (eq_sub_iff_add_eq).mpr (h x).symm
          _ = f x + (b - c) := by abel
    · rintro ⟨d, hb, hg⟩ x
      rw [hg x, hb]
      abel
  · intro X V _ f g b c k x₀ h hf hg
    have hc : b = c := by
      have hx := h x₀
      rw [hf, hg] at hx
      exact add_left_cancel hx
    refine ⟨hc, ?_⟩
    intro x
    have hx := h x
    rw [hc] at hx
    exact add_right_cancel hx
  · refine ⟨(fun _ => 0), (fun _ => 1), 1, 0, ?_, ?_, ?_⟩
    · intro x; rfl
    · intro x; change (0 : Int) ≠ 1; decide
    · decide
  · refine ⟨(fun _ => 0), (fun x => if x then 1 else 0),
      (fun _ => 0), (fun x => if x then -1 else 0), ?_, rfl, ?_⟩
    · intro x; cases x <;> decide
    · decide
end TruthCore.Results.Science.MeasurementCalibration
