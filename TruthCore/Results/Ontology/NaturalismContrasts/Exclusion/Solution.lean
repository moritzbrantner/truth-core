module

public import TruthCore.Ontology.NaturalismContrasts
public import TruthCore.Results.Ontology.NaturalismContrasts.Population.Solution

@[expose] public section

namespace TruthCore.Results.Ontology.NaturalismContrasts.Exclusion

open TruthCore.Ontology.NaturalismContrasts TruthCore.Ontology.Naturalism TruthCore.Ontology.Spatiotemporal
open TruthCore.German.Kant.CosmologicalInference (Ontic)

theorem noExistingSimpleRemote {W B : Type} (o : Ontic W B) (F : Frame B)
    (ComponentOf : B → B → Prop) (Composite : B → Prop) (w : W)
    (hN1 : ExistenceNaturalism o (PartOfSpacetime F) w)
    (hParts : ExistingProperPartsAreComponents o F ComponentOf w)
    (hComponents : ExistingComponentsMakeWholeComposite o F ComponentOf Composite w)
    (hTwo : TwoExist o w) : NoExistingSimpleRemote o ComponentOf Composite w := by
  intro hCandidate
  exact Population.remoteSimplePopulationConstraint o F ComponentOf Composite w
    hN1 hParts hComponents hCandidate hTwo

end TruthCore.Results.Ontology.NaturalismContrasts.Exclusion
