module

public import TruthCore.Ontology.NaturalismConsequences
public import TruthCore.Results.Ontology.Naturalism.Outside.Solution

@[expose] public section

namespace TruthCore.Results.Ontology.Naturalism.RefutesN2
open TruthCore.German.Kant.CosmologicalInference (Ontic)
open TruthCore.Ontology.Spatiotemporal
open TruthCore.Ontology.Naturalism
open TruthCore.Ontology.NaturalismConsequences
open TruthCore.Latin.Aquinas.SummaTheologiae (NothingIsEfficientCauseOfItselfReading)

/-- With the weak causal-concreteness floor item in place of N1's unrestricted domain: the existing cause of the spacetime whole is concrete, so N2 would make it a part of spacetime; so N2 fails. -/
theorem causedUniverseRefutesN2 {W B : Type} (o : Ontic W B) (F : Frame B) (concrete P : B → Prop)
    (hasCausalPower : W → B → Prop) (w : W)
    (hCaused : UniverseHasExistingCause o F w)
    (hBridge : CausingWholeCausesParts o F w)
    (hSelf : NothingIsEfficientCauseOfItselfReading (fun x y (_ : Unit) => o.Causes w x y))
    (hContained : ContainedInSpacetime F P)
    (hFloor : TruthCore.Causality.CausalPowerConcreteness.OwnerCommitmentAt o concrete hasCausalPower w) :
    ConcreteNaturalismFails o concrete P w :=
  fun hN =>
    match hCaused with
    | ⟨c, hc, hcw⟩ =>
      Outside.universeCauseOutsideSpacetime o F w hBridge hSelf c hcw
        (hContained c (hN c hc (hFloor.2 c F.whole hcw)))

end TruthCore.Results.Ontology.Naturalism.RefutesN2
