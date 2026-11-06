module

public import TruthCore.Ontology.NaturalismSets
public import TruthCore.Results.Ontology.NaturalismSets.Unlocation.Solution

@[expose] public section

namespace TruthCore.Results.Ontology.NaturalismSets
open TruthCore.Ontology.NaturalismSets TruthCore.Ontology.Naturalism
open TruthCore.Ontology.Spatiotemporal
open TruthCore.German.Kant.CosmologicalInference (Ontic)

theorem absent {W B S : Type} (decode : S → ZFSet.{0})
    (o : Ontic W (B ⊕ S)) (F : Frame (B ⊕ S)) (w : W)
    (hN1 : ExistenceNaturalism o (Located F) w)
    (hSupport : SetLocationHasMemberSupport decode F) :
    NoExistingSetRepresentatives o w := by
  intro s hs
  exact unlocated decode F hSupport s (hN1 (.inr s) hs)

end TruthCore.Results.Ontology.NaturalismSets
