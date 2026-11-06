import TruthCore.Ontology.NaturalismConsequences
namespace TruthCore.Results.Ontology.Naturalism.Atemporal
open TruthCore.German.Kant.CosmologicalInference (Ontic)
open TruthCore.Ontology.Spatiotemporal
open TruthCore.Ontology.Naturalism
open TruthCore.Ontology.NaturalismConsequences
open TruthCore.Latin.Aquinas.SummaTheologiae (NothingIsEfficientCauseOfItselfReading)
/-- Strong version: if moreover whatever is successively temporal in some supplied
temporal series is a part of the spacetime whole (no supplied series has a
successive bearer outside this spacetime), no cause of the whole is successively
temporal in any supplied series. -/
theorem universeCauseAtemporal {W B I : Type} (o : Ontic W B) (F : Frame B) (w : W)
    (S : I → TemporalSeries B)
    (hBridge : CausingWholeCausesParts o F w)
    (hSelf : NothingIsEfficientCauseOfItselfReading (fun x y (_ : Unit) => o.Causes w x y))
    (hTemporal : TemporalContainedInSpacetime F S) :
    CausesOfUniverseAtemporal o F w S := by
  sorry
end TruthCore.Results.Ontology.Naturalism.Atemporal
