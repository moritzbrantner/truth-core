module

public import TruthCore.Ontology.NaturalismContrasts

@[expose] public section

namespace TruthCore.Results.Ontology.NaturalismContrasts.Population

open TruthCore.Ontology.NaturalismContrasts TruthCore.Ontology.Naturalism TruthCore.Ontology.Spatiotemporal
open TruthCore.German.Kant.CosmologicalInference (Ontic)

theorem remoteSimplePopulationConstraint {W B : Type} (o : Ontic W B) (F : Frame B)
    (ComponentOf : B → B → Prop) (Composite : B → Prop) (w : W)
    (hN1 : ExistenceNaturalism o (PartOfSpacetime F) w)
    (hParts : ExistingProperPartsAreComponents o F ComponentOf w)
    (hComponents : ExistingComponentsMakeWholeComposite o F ComponentOf Composite w) :
    RemoteSimplePopulationConstraint o ComponentOf Composite w := by
  rintro ⟨g, hExistsG, hSimpleG, hRemoteG⟩ ⟨x, y, hExistsX, hExistsY, hDistinct⟩
  have hGNotProper : ¬ (g ≠ F.whole) := by
    intro hProper
    exact hRemoteG F.whole (hParts g hExistsG (hN1 g hExistsG) hProper)
  have hWholeSimple : ¬ Composite F.whole := by
    intro hComposite
    apply hGNotProper
    intro hIdentity
    exact hSimpleG (hIdentity.symm ▸ hComposite)
  have hNoProper : ∀ z, o.ExistsAt w z → ¬ (z ≠ F.whole) := by
    intro z hExists hProper
    exact hWholeSimple (hComponents z hExists
      (hParts z hExists (hN1 z hExists) hProper) hProper)
  apply hNoProper x hExistsX
  intro hXWhole
  apply hNoProper y hExistsY
  intro hYWhole
  exact hDistinct (hXWhole.trans hYWhole.symm)

end TruthCore.Results.Ontology.NaturalismContrasts.Population
