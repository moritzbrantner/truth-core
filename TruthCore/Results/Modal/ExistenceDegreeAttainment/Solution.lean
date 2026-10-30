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
  have hLocal : ∀ v, m.frame.access w₀ v → ∀ y, m.ExistsAt v y →
      intensity v y ≤ intensity v n := by
    intro v hv y hy
    rcases hEM (y = n) with hSame | hOther
    · subst y
      exact le_refl _
    · exact hBound v hv n y (hNecessary v hv) hy (hPotential v hv y hy hOther)
  constructor
  · rintro ⟨v, x, hv, hx, hAll⟩
    refine ⟨intensity v n, ⟨v, hv, rfl⟩, ?_⟩
    rintro d ⟨u, hu, rfl⟩
    exact le_trans (hAll u hu n (hNecessary u hu)) (hLocal v hv x hx)
  · rintro ⟨d, hGreatest⟩
    obtain ⟨v, hv, hvd⟩ := hGreatest.1
    refine ⟨v, n, hv, hNecessary v hv, ?_⟩
    intro u hu y hy
    have hOwn : intensity u n ≤ d := hGreatest.2 ⟨u, hu, rfl⟩
    rw [← hvd] at hOwn
    exact le_trans (hLocal u hu y hy) hOwn

end TruthCore.Results.Modal.ExistenceDegreeAttainment
