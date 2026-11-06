import TruthCore.Ontology.NaturalismConsequences
namespace TruthCore.Results.Ontology.Naturalism.RefutesN3i
open TruthCore.German.Kant.CosmologicalInference (Ontic)
open TruthCore.Ontology.Spatiotemporal
open TruthCore.Ontology.Naturalism
open TruthCore.Ontology.NaturalismConsequences
open TruthCore.Latin.Aquinas.SummaTheologiae (NothingIsEfficientCauseOfItselfReading)
/-- If moreover the spacetime whole satisfies the thesis predicate, its cause causes something satisfying it, so N3i would make the cause a part of spacetime; so N3i fails. -/
theorem causedUniverseRefutesN3Interaction {W B : Type} (o : Ontic W B) (F : Frame B) (P : B → Prop) (w : W)
    (hCaused : UniverseHasExistingCause o F w)
    (hBridge : CausingWholeCausesParts o F w)
    (hSelf : NothingIsEfficientCauseOfItselfReading (fun x y (_ : Unit) => o.Causes w x y))
    (hContained : ContainedInSpacetime F P)
    (hWhole : WholeSatisfies F P) :
    InteractionNaturalismFails o P w := by
  sorry
end TruthCore.Results.Ontology.Naturalism.RefutesN3i
