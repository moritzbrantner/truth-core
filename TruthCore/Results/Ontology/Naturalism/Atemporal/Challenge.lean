import TruthCore.Ontology.NaturalismConsequences
namespace TruthCore.Results.Ontology.Naturalism.Atemporal
open TruthCore.German.Kant.CosmologicalInference (Ontic)
open TruthCore.Ontology.Spatiotemporal
open TruthCore.Ontology.Naturalism
open TruthCore.Ontology.NaturalismConsequences
open TruthCore.Latin.Aquinas.SummaTheologiae (NothingIsEfficientCauseOfItselfReading)
/-- Strong version: if moreover every temporal thing is a part of the spacetime whole (no time outside this spacetime), every cause of the whole is not temporal at all. -/
theorem universeCauseAtemporal {W B : Type} (o : Ontic W B) (F : Frame B) (w : W) (temporal : B → Prop)
    (hBridge : CausingWholeCausesParts o F w)
    (hSelf : NothingIsEfficientCauseOfItselfReading (fun x y (_ : Unit) => o.Causes w x y))
    (hTemporal : TemporalContainedInSpacetime F temporal) :
    CausesOfUniverseAtemporal o F w temporal := by
  sorry
end TruthCore.Results.Ontology.Naturalism.Atemporal
