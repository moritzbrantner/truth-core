import TruthCore.Causality.Supertasks

namespace TruthCore.Results.Causality.SupertaskFinitePrefixShift
open TruthCore.Causality

/-- A concrete natural-number capacity countermodel to the quantifier shift. -/
theorem supertaskFinitePrefixShift : FinitePrefixesFitSeparatelyNotUniformly := by
  constructor
  · intro segmentLength
    exact ⟨segmentLength, Nat.le_refl segmentLength⟩
  · rintro ⟨capacity, hCapacity⟩
    exact (Nat.not_succ_le_self capacity) (hCapacity (capacity + 1))

end TruthCore.Results.Causality.SupertaskFinitePrefixShift
