import TruthCore.Ontology.NaturalismContrasts

namespace TruthCore.Results.Ontology.NaturalismContrasts.Population

open TruthCore.Ontology.NaturalismContrasts TruthCore.Ontology.Naturalism TruthCore.Ontology.Spatiotemporal
open TruthCore.German.Kant.CosmologicalInference (Ontic)

theorem remoteSimplePopulationConstraint {W B : Type} (o : Ontic W B) (F : Frame B)
    (ComponentOf : B → B → Prop) (Composite : B → Prop) (w : W)
    (hN1 : ExistenceNaturalism o (PartOfSpacetime F) w)
    (hParts : ExistingProperPartsAreComponents o F ComponentOf w)
    (hComponents : ExistingComponentsMakeWholeComposite o F ComponentOf Composite w) :
    RemoteSimplePopulationConstraint o ComponentOf Composite w := by
  sorry

end TruthCore.Results.Ontology.NaturalismContrasts.Population
