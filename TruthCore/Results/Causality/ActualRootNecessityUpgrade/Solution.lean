import TruthCore.Causality.ActualRootUniqueness
import TruthCore.Causality.NecessaryRootUniqueness

namespace TruthCore.Results.Causality.ActualRootNecessityUpgrade
open TruthCore.Causality.BruteFoundationBoundary (Profile EveryContingentGroundedAt)
open TruthCore.Causality.NecessaryRootFork
open TruthCore.Causality.ActualRootUniqueness
open TruthCore.Causality.NecessaryRootUniqueness
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt)
open TruthCore.Logic (ExcludedMiddle)

/-- Restore necessity to the SAME unique actual root with the existing
contingent-root exclusion. No new foundation or actuality premise is hidden. -/
theorem upgrade {W B : Type} (m : Profile W B) (w : W)
    (hUnique : UniqueActualRootAt m w)
    (hDep : EveryContingentGroundedAt m w) (hEM : ExcludedMiddle) :
    UniqueNecessaryActualRootAt m w := by
  obtain ⟨n, hn, hUnicity⟩ := hUnique
  cases hEM (NecessaryAt m.ontic w n) with
  | inl hNecessary => exact ⟨n, hn, hNecessary, hUnicity⟩
  | inr hNotNecessary =>
    exact False.elim
      ((everyContingentGrounded_iff_noContingentRoot m w hEM).mp hDep
        (contingentRootOfNonnecessary m w hEM ⟨n, hn, hNotNecessary⟩))

end TruthCore.Results.Causality.ActualRootNecessityUpgrade
