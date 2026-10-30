import TruthCore.Modal.BoundedMetricPastControl
namespace TruthCore.Results.Modal.BoundedMetricPast
open TruthCore.Modal.BoundedMetricPast
open TruthCore.Latin.Aquinas.SummaTheologiae

theorem checks : BoundedMetricPastControl := by
  let now : Set.Ioc (0 : ℝ) 1 := ⟨1, by constructor <;> linarith⟩
  have hInfinite :
      PastIsInfinite (fun s t : Set.Ioc (0 : ℝ) 1 => s.val < t.val) now := by
    intro t _
    have hHalf : t.val / 2 ∈ Set.Ioc (0 : ℝ) 1 := by
      constructor <;> nlinarith [t.property.1, t.property.2]
    refine ⟨⟨t.val / 2, hHalf⟩, ?_⟩
    change t.val / 2 < t.val
    nlinarith [t.property.1]
  refine ⟨now, rfl, hInfinite, ?_, ?_⟩
  · rintro ⟨t, ht, hFirst⟩
    obtain ⟨s, hs⟩ := hInfinite t ht
    exact hFirst s hs
  · intro t
    change 0 ≤ 1 - t.val ∧ 1 - t.val < 1
    constructor <;> linarith [t.property.1, t.property.2]
end TruthCore.Results.Modal.BoundedMetricPast
