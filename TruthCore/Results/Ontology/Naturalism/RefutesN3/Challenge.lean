import TruthCore.Ontology.NaturalismConsequences
namespace TruthCore.Results.Ontology.Naturalism.RefutesN3
open TruthCore.German.Kant.CosmologicalInference (Ontic)
open TruthCore.Ontology.Spatiotemporal
open TruthCore.Ontology.Naturalism
open TruthCore.Ontology.NaturalismConsequences
open TruthCore.Latin.Aquinas.SummaTheologiae (NothingIsEfficientCauseOfItselfReading)
/-- With the exercise-to-power reading: the cause of the spacetime whole has causal power, so N3 would make it a part of spacetime; so N3 fails. -/
theorem causedUniverseRefutesN3 {W B : Type} (o : Ontic W B) (F : Frame B) (P : B → Prop)
    (hasCausalPower : W → B → Prop) (w : W)
    (hCaused : UniverseHasExistingCause o F w)
    (hBridge : CausingWholeCausesParts o F w)
    (hSelf : NothingIsEfficientCauseOfItselfReading (fun x y (_ : Unit) => o.Causes w x y))
    (hContained : ContainedInSpacetime F P)
    (hExercise : CausingExercisesPower o hasCausalPower w) :
    CausalPowerNaturalismFails hasCausalPower P w := by
  sorry
end TruthCore.Results.Ontology.Naturalism.RefutesN3
