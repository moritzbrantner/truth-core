import TruthCore.Modal.ExistenceDegreeAttainment

namespace TruthCore.Results.Modal.ExistenceDegreeAttainment
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Modal.ExistenceDegrees

/-- Under the per-world weak causal profile, a possible global maximum exists
exactly when the selected necessary individual's own accessible-world degree
family attains a greatest member. No invariance or actual-reflexivity premise
is used. Both sides are false on an empty accessible family, so no nonemptiness
is hidden. This concerns possible attainment, not n being globally maximal at
every world, value, actual causal exercise or uniqueness. -/
theorem attainmentIff {World Being Degree : Type} [Preorder Degree]
    (m : Ontic World Being) (intensity : World → Being → Degree)
    (w₀ : World) (n : Being)
    (hNecessary : NecessaryAt m w₀ n)
    (hPotential : OtherDirectedPotentialCause m w₀ n)
    (hBound : WeakCauseDegreeBound m intensity w₀)
    (hEM : TruthCore.Logic.ExcludedMiddle) :
    GlobalAttainmentIffSelectedFamily m intensity w₀ n := by
  sorry

end TruthCore.Results.Modal.ExistenceDegreeAttainment
