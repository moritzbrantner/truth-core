import TruthCore.Ontology.NaturalismSets
namespace TruthCore.Results.Ontology.NaturalismSets
open TruthCore.Ontology.NaturalismSets TruthCore.Ontology.Naturalism
open TruthCore.Ontology.Spatiotemporal
open TruthCore.German.Kant.CosmologicalInference (Ontic)

theorem absent {W B S : Type} (decode : S → ZFSet.{0})
    (o : Ontic W (B ⊕ S)) (F : Frame (B ⊕ S)) (w : W)
    (hN1 : ExistenceNaturalism o (Located F) w)
    (hSupport : SetLocationHasMemberSupport decode F) :
    NoExistingSetRepresentatives o w := by
  sorry

end TruthCore.Results.Ontology.NaturalismSets
