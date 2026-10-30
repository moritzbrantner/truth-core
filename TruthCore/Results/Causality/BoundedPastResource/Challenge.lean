import TruthCore.Causality.BoundedPastResource

namespace TruthCore.Results.Causality.BoundedPastResource
open TruthCore.Causality.BoundedPastResource

/-- A real stock cannot have both a lower bound on a beginningless integer
past and one uniform positive increment at every forward unit step. This is a
conditional constraint on that profile, not a claim that physical entropy or
the universe satisfies these assumptions. -/
theorem noUniformGrowth (S : Int → ℝ) (now : Int) (ε L : ℝ)
    (hPositive : PositiveStep ε)
    (hLower : PastLowerBound S now L)
    (hGrowth : UniformPastGrowth S now ε) :
    TruthCore.Logic.ConfigurationFalse := by
  sorry

end TruthCore.Results.Causality.BoundedPastResource
