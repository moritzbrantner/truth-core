import TruthCore.Mereology.NecessaryPartFusionDecomposition

namespace TruthCore.Results.Mereology.NecessaryPartFusionDecomposition
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Mereology.UniversalFusionBoundary
open TruthCore.Mereology.FusionNoNecessaryParts
open TruthCore.Mereology.NecessaryPartFusionDecomposition

/-- Fusion's no-extra-parts clause and overlap extensionality place the selected
necessary-parts fusion within the original x. No modal closure law is used. -/
theorem fusionBelow {W B : Type} [PartialOrder B] (m : Ontic W B) (w : W)
    (x n : B) (hExtensional : OverlapExtensionalParthood B)
    (hFusion : Fusion (necessaryParts m w x) n) : n ≤ x := by
  apply (hExtensional n x).mpr
  intro z hOverlap
  obtain ⟨p, hpz, hpn⟩ := hOverlap
  obtain ⟨s, hs, q, hqp, hqs⟩ := hFusion.2 p hpn
  exact ⟨q, le_trans hqp hpz, le_trans hqs hs.1⟩

/-- A nonnecessary object has a part without necessary parts under explicit
overlap-extensional parthood and the selected necessary-fusion warrant. -/
theorem decompose {W B : Type} [PartialOrder B] (m : Ontic W B) (w : W) (x : B)
    (hNotNecessary : NotNecessaryAt m w x)
    (hExtensional : OverlapExtensionalParthood B)
    (hFusion : SelectedNecessaryPartsFusionAt m w x) :
    HasNoNecessaryPartsPartAt m w x := by
  rcases Classical.em ((necessaryParts m w x).Nonempty) with hSome | hNone
  · obtain ⟨n, hSum, hn⟩ := hFusion hSome
    have hnx : n ≤ x := fusionBelow m w x n hExtensional hSum
    have hNotBelow : ¬ x ≤ n := by
      intro hxn
      have hEq : x = n := le_antisymm hxn hnx
      exact hNotNecessary (hEq.symm ▸ hn)
    have hSeparate : ∃ z, Overlap z x ∧ ¬ Overlap z n := by
      apply Classical.byContradiction
      intro hNoSeparation
      apply hNotBelow
      apply (hExtensional x n).mpr
      intro z hzx
      apply Classical.byContradiction
      intro hzn
      exact hNoSeparation ⟨z, hzx, hzn⟩
    obtain ⟨z, ⟨q, hqz, hqx⟩, hDisjoint⟩ := hSeparate
    refine ⟨q, hqx, ?_⟩
    intro r hrq hrNecessary
    have hrMember : r ∈ necessaryParts m w x := ⟨le_trans hrq hqx, hrNecessary⟩
    exact hDisjoint ⟨r, le_trans hrq hqz, hSum.1 r hrMember⟩
  · refine ⟨x, le_refl x, ?_⟩
    intro p hpx hpNecessary
    exact hNone ⟨p, hpx, hpNecessary⟩

end TruthCore.Results.Mereology.NecessaryPartFusionDecomposition
