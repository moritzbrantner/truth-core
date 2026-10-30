import TruthCore.Models.PastResourceControls

namespace TruthCore.Results.Causality.PastResourceControls
open TruthCore.Causality.BoundedPastResource
open TruthCore.Models.PastResourceControls

theorem expLowerBound : PastLowerBound expStock 0 0 := by
  intro t _
  exact (Real.exp_pos (t : ℝ)).le

theorem expStrictGrowth : ∀ t : Int, t < 0 → expStock t < expStock (t + 1) := by
  intro t _
  apply Real.exp_lt_exp.mpr
  simpa only [Int.cast_add, Int.cast_one] using (lt_add_one (t : ℝ))

theorem expNoUniformPositiveGrowth :
    ¬ ∃ ε : ℝ, PositiveStep ε ∧ UniformPastGrowth expStock 0 ε := by
  rintro ⟨ε, hPositive, hGrowth⟩
  exact TruthCore.Results.Causality.BoundedPastResource.noUniformGrowth
    expStock 0 ε 0 hPositive expLowerBound hGrowth

theorem linearUnitGrowth : UniformPastGrowth linearStock 0 1 := by
  intro t _
  change (t : ℝ) + 1 ≤ ((t + 1 : Int) : ℝ)
  simp only [Int.cast_add, Int.cast_one, le_refl]

theorem linearNoPastLowerBound : ¬ ∃ L : ℝ, PastLowerBound linearStock 0 L := by
  rintro ⟨L, hLower⟩
  exact TruthCore.Results.Causality.BoundedPastResource.noUniformGrowth
    linearStock 0 1 L zero_lt_one hLower linearUnitGrowth

/-- Compose the independently proved resource constraint with each retained
positive assignment. Neither omitted condition follows from its rival. -/
theorem controls : TruthCore.Models.PastResourceControls.JointControls := by
  exact ⟨⟨expLowerBound, expStrictGrowth, expNoUniformPositiveGrowth⟩,
    ⟨zero_lt_one, linearUnitGrowth, linearNoPastLowerBound⟩⟩
end TruthCore.Results.Causality.PastResourceControls
