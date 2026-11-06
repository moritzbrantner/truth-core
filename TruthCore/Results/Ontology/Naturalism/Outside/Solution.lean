module

public import TruthCore.Ontology.NaturalismConsequences

@[expose] public section

namespace TruthCore.Results.Ontology.Naturalism.Outside
open TruthCore.German.Kant.CosmologicalInference (Ontic)
open TruthCore.Ontology.Spatiotemporal
open TruthCore.Ontology.Naturalism
open TruthCore.Ontology.NaturalismConsequences
open TruthCore.Latin.Aquinas.SummaTheologiae (NothingIsEfficientCauseOfItselfReading)

/-- Every cause of the spacetime whole lies outside spacetime: if it were a part, by the whole-to-part bridge it would cause itself, which nothing does. -/
theorem universeCauseOutsideSpacetime {W B : Type} (o : Ontic W B) (F : Frame B) (w : W)
    (hBridge : CausingWholeCausesParts o F w)
    (hSelf : NothingIsEfficientCauseOfItselfReading (fun x y (_ : Unit) => o.Causes w x y)) :
    CausesOfUniverseOutsideSpacetime o F w :=
  fun c hc hp => hSelf c () (hBridge c c hc hp)

end TruthCore.Results.Ontology.Naturalism.Outside
