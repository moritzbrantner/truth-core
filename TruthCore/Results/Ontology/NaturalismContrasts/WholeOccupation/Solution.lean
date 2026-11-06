module

public import TruthCore.Ontology.NaturalismContrasts

@[expose] public section

namespace TruthCore.Results.Ontology.NaturalismContrasts.WholeOccupation

open TruthCore.Ontology.NaturalismContrasts TruthCore.Ontology.Naturalism TruthCore.Ontology.Spatiotemporal
open TruthCore.German.Kant.CosmologicalInference (Ontic)

theorem wholeOccupationBoundary {W B : Type} (o : Ontic W B) (F : Frame B) (w : W)
    (hN1 : ExistenceNaturalism o (Located F) w) (hUnlocated : WholeUnlocated F) :
    WholeAbsent o F w := by
  intro hExists
  exact hUnlocated (hN1 F.whole hExists)

end TruthCore.Results.Ontology.NaturalismContrasts.WholeOccupation
