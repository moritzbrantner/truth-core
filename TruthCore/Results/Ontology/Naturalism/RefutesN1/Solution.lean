module

public import TruthCore.Ontology.NaturalismConsequences
public import TruthCore.Results.Ontology.Naturalism.Outside.Solution

@[expose] public section

namespace TruthCore.Results.Ontology.Naturalism.RefutesN1
open TruthCore.German.Kant.CosmologicalInference (Ontic)
open TruthCore.Ontology.Spatiotemporal
open TruthCore.Ontology.Naturalism
open TruthCore.Ontology.NaturalismConsequences
open TruthCore.Latin.Aquinas.SummaTheologiae (NothingIsEfficientCauseOfItselfReading)

/-- If the spacetime whole has an existing cause, causing the whole causes its parts, nothing causes itself and the thesis predicate is contained in spacetime, then N1 fails: the existing cause would satisfy the predicate, hence be a part of spacetime. -/
theorem causedUniverseRefutesN1 {W B : Type} (o : Ontic W B) (F : Frame B) (P : B → Prop) (w : W)
    (hCaused : UniverseHasExistingCause o F w)
    (hBridge : CausingWholeCausesParts o F w)
    (hSelf : NothingIsEfficientCauseOfItselfReading (fun x y (_ : Unit) => o.Causes w x y))
    (hContained : ContainedInSpacetime F P) :
    ExistenceNaturalismFails o P w :=
  fun hN =>
    match hCaused with
    | ⟨c, hc, hcw⟩ =>
      Outside.universeCauseOutsideSpacetime o F w hBridge hSelf c hcw (hContained c (hN c hc))

end TruthCore.Results.Ontology.Naturalism.RefutesN1
