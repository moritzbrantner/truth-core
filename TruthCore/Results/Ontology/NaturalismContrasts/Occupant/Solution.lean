module

public import TruthCore.Results.Ontology.NaturalismContrasts.Exclusion.Solution
public import TruthCore.Ontology.NaturalismConsequences

@[expose] public section

namespace TruthCore.Results.Ontology.NaturalismContrasts.Occupant

open TruthCore.Ontology.NaturalismContrasts TruthCore.Ontology.Naturalism TruthCore.Ontology.Spatiotemporal
open TruthCore.Ontology.NaturalismConsequences (ContainedInSpacetime)
open TruthCore.German.Kant.CosmologicalInference (Ontic)

/-- Occupation reaches the part-based exclusion only through the separately
supplied, existing thesis-containment bridge. -/
theorem occupantNoExistingSimpleRemote {W B : Type} (o : Ontic W B) (F : Frame B)
    (ComponentOf : B → B → Prop) (Composite : B → Prop) (w : W)
    (hN1 : ExistenceNaturalism o (Located F) w)
    (hContained : ContainedInSpacetime F (Located F))
    (hParts : ExistingProperPartsAreComponents o F ComponentOf w)
    (hComponents : ExistingComponentsMakeWholeComposite o F ComponentOf Composite w)
    (hTwo : TwoExist o w) : NoExistingSimpleRemote o ComponentOf Composite w := by
  have hPartN1 : ExistenceNaturalism o (PartOfSpacetime F) w :=
    fun x hx => hContained x (hN1 x hx)
  exact Exclusion.noExistingSimpleRemote o F ComponentOf Composite w
    hPartN1 hParts hComponents hTwo

end TruthCore.Results.Ontology.NaturalismContrasts.Occupant
