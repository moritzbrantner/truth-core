module

public import TruthCore.Causality.MaximumDefinitionFork

@[expose] public section
namespace TruthCore.Results.Causality.MaximumDefinitions.DirectedBridge
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Causality.MaximumDefinitionFork

/-- Frozen analyst interface; no real-world degree interpretation is adopted. -/
theorem directedBridge {Degree : Type} [Preorder Degree] (f : Frame Degree)
    (hEM : TruthCore.Logic.ExcludedMiddle)
    (hCalibration : StrictDegreeCalibration f) (hDirected : DirectedBearers f) :
    MaximalToGreatest f := by
  intro m hm
  refine ⟨hm.1, ⟨⟨m, hm.1, rfl⟩, ?_⟩⟩
  intro d hd
  obtain ⟨x, hx, hValue⟩ := hd
  rw [← hValue]
  obtain ⟨z, hz, hmz, hxz⟩ := hDirected m x hm.1 hx
  have hNotStrict : ¬ f.value m < f.value z := by
    intro hlt
    exact hm.2 z ((hCalibration z m hz hm.1).mpr hlt)
  have hzm : f.value z ≤ f.value m := by
    cases hEM (f.value z ≤ f.value m) with
    | inl h => exact h
    | inr h => exact False.elim (hNotStrict (lt_iff_le_not_ge.mpr ⟨hmz, h⟩))
  exact le_trans hxz hzm

end TruthCore.Results.Causality.MaximumDefinitions.DirectedBridge
