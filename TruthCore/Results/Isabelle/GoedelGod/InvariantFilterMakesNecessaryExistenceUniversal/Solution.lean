import TruthCore.Isabelle.AFP.GoedelGod

namespace TruthCore.Results.Isabelle.GoedelGod.InvariantFilterMakesNecessaryExistenceUniversal

open TruthCore.Isabelle.AFP.GoedelGod

/-- Every admitted essence contains the bearer at the current world. Its
world-invariance carries that same bearer to every accessible world, without
using accessibility conditions, positivity or classical logic. -/
theorem checks {World Ind : Type} : InvariantFilterMakesNecessaryExistenceUniversal World Ind := by
  intro F x w Φ hInvariant hEss next _
  exact ⟨x, (hInvariant x w next).mp hEss.1⟩

end TruthCore.Results.Isabelle.GoedelGod.InvariantFilterMakesNecessaryExistenceUniversal
