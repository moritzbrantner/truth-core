import TruthCore.Ontology.NaturalismContrasts
import TruthCore.Ontology.NaturalismConsequences

namespace TruthCore.Results.Ontology.NaturalismContrasts.Occupant

open TruthCore.Ontology.NaturalismContrasts TruthCore.Ontology.Naturalism TruthCore.Ontology.Spatiotemporal
open TruthCore.Ontology.NaturalismConsequences (ContainedInSpacetime)
open TruthCore.German.Kant.CosmologicalInference (Ontic)

theorem occupantNoExistingSimpleRemote {W B : Type} (o : Ontic W B) (F : Frame B)
    (ComponentOf : B → B → Prop) (Composite : B → Prop) (w : W)
    (hN1 : ExistenceNaturalism o (Located F) w)
    (hContained : ContainedInSpacetime F (Located F))
    (hParts : ExistingProperPartsAreComponents o F ComponentOf w)
    (hComponents : ExistingComponentsMakeWholeComposite o F ComponentOf Composite w)
    (hTwo : TwoExist o w) : NoExistingSimpleRemote o ComponentOf Composite w := by
  sorry

end TruthCore.Results.Ontology.NaturalismContrasts.Occupant
