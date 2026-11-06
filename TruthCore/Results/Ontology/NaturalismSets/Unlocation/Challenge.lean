import TruthCore.Ontology.NaturalismSets
namespace TruthCore.Results.Ontology.NaturalismSets
open TruthCore.Ontology.NaturalismSets TruthCore.Ontology.Naturalism
open TruthCore.Ontology.Spatiotemporal
open TruthCore.German.Kant.CosmologicalInference (Ontic)

theorem unlocated {B S : Type} (decode : S → ZFSet.{0}) (F : Frame (B ⊕ S))
    (h : SetLocationHasMemberSupport decode F) : SetRepresentativesUnlocated F := by
  sorry

end TruthCore.Results.Ontology.NaturalismSets
