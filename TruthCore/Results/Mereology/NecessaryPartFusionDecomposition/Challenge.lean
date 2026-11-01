import TruthCore.Mereology.NecessaryPartFusionDecomposition

namespace TruthCore.Results.Mereology.NecessaryPartFusionDecomposition
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Mereology.NecessaryPartFusionDecomposition

/-- A nonnecessary object has a part without necessary parts under explicit
overlap-extensional parthood and the selected necessary-fusion warrant. -/
theorem decompose {W B : Type} [PartialOrder B] (m : Ontic W B) (w : W) (x : B)
    (hNotNecessary : NotNecessaryAt m w x)
    (hExtensional : OverlapExtensionalParthood B)
    (hFusion : SelectedNecessaryPartsFusionAt m w x) :
    HasNoNecessaryPartsPartAt m w x := by
  sorry

end TruthCore.Results.Mereology.NecessaryPartFusionDecomposition
