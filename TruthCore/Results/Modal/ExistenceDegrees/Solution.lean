import TruthCore.Modal.ExistenceDegrees

namespace TruthCore.Results.Modal.ExistenceDegrees
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Causality.NecessarilyUnderived (ActualReflexive)
open TruthCore.Modal.ExistenceDegrees

/-- The selected necessary individual is a global existence-degree maximum at
every root-accessible world, under the explicit singular other-directed
pointwise profile. Its actual existence follows from actual accessibility
and necessity. Possible effects need not share a causal witness world.
No possible-maximum premise from source step 5 is used. The result says nothing
about value (step 4), actual causal exercise, God or uniqueness. -/
theorem necessaryGlobalMaximum {World Being Degree : Type} [Preorder Degree]
    (m : Ontic World Being) (intensity : World → Being → Degree)
    (w₀ : World) (n : Being)
    (hActual : ActualReflexive m w₀)
    (hNecessary : NecessaryAt m w₀ n)
    (hPotential : OtherDirectedPotentialCause m w₀ n)
    (hBound : WeakCauseDegreeBound m intensity w₀)
    (hInvariant : NecessaryDegreeInvariant m intensity w₀ n)
    (hEM : TruthCore.Logic.ExcludedMiddle) :
    NecessaryGlobalDegreeMaximum m intensity w₀ n := by
  have hStable := hInvariant hNecessary
  refine ⟨hNecessary w₀ hActual, hNecessary, ?_⟩
  intro v hv u hu y hy
  have hLocal : intensity u y ≤ intensity u n := by
    rcases hEM (y = n) with hSame | hOther
    · subst y
      exact le_refl _
    · exact hBound u hu n y (hNecessary u hu) hy (hPotential u hu y hy hOther)
  exact le_trans (le_trans hLocal (hStable u hu).1) (hStable v hv).2

/-- The named individual's global-at-every-world conclusion gives an attained
possible maximum at the actual world when that world accesses itself. This
keeps mere possible attainment distinct from the stronger named conclusion. -/
theorem attainedFromNamed {World Being Degree : Type} [Preorder Degree]
    (m : Ontic World Being) (intensity : World → Being → Degree)
    (w₀ : World) (n : Being)
    (hActual : ActualReflexive m w₀)
    (hMaximum : NecessaryGlobalDegreeMaximum m intensity w₀ n) :
    AttainedGlobalDegreeMaximum m intensity w₀ := by
  refine ⟨w₀, n, hActual, hMaximum.1, ?_⟩
  intro u hu y hy
  exact hMaximum.2.2 w₀ hActual u hu y hy

end TruthCore.Results.Modal.ExistenceDegrees
