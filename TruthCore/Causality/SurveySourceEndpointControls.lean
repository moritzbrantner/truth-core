module

public import TruthCore.Causality.PossibleCausalSourceNecessity
public import TruthCore.Causality.PossibleCauseOfContingency
public import TruthCore.Causality.BruteFoundationBoundary

/-! Exact endpoint obstruction for the A2 application. These finite controls
are analyst interpretations, not definitions of the two original capability
senses. The necessary individual is actually present, but isolated and outside
the supplied concrete predicate. No real-world applicability is claimed. -/

@[expose] public section
namespace TruthCore.Causality.SurveySourceEndpointControls
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Causality.WorldSourceRegress
open TruthCore.Causality.HeadlessCausalAncestry
open TruthCore.Causality.PossibleCausalSourceNecessity
open TruthCore.Causality.NecessarilyUnderived

/-- One actually present rigid individual; no causal exercise in either direction. -/
def isolated : Ontic Unit Unit where
  frame := ⟨fun _ _ => True⟩
  ExistsAt := fun _ _ => True
  Causes := fun _ _ _ => False

/-- No candidate is concrete in this interpretation. Grounding is independent
of ordinary causation and empty; no identification of the two is used. -/
def abstractProfile : TruthCore.Causality.BruteFoundationBoundary.Profile Unit Unit where
  ontic := isolated
  concrete := fun _ => False
  grounds := fun _ _ _ => False

/-- All four nonlogical inputs of the existing source-necessity composition
hold jointly, and its SAME actual source is necessary. Nevertheless neither
outgoing actual causation nor the exact necessary-concrete route node follows.
EM is not assigned an intuitionistic independence interpretation. -/
def EndpointObstruction : Prop :=
  LocalCausalPrinciple isolated ∧
  TruthCore.Modal.Euclidean isolated.frame ∧
  ActualReflexive isolated () ∧
  PossiblyFailedHeadlessCoverage isolated () ∧
  (∃ c, isolated.ExistsAt () c ∧ NecessaryAt isolated () c ∧
    (actualGraph isolated ()).Source ⟨c, True.intro⟩) ∧
  (¬ ∃ c e, isolated.Causes () c e) ∧
  ¬ TruthCore.Causality.BruteFoundationBoundary.NecessaryConcreteAt abstractProfile ()

end TruthCore.Causality.SurveySourceEndpointControls
