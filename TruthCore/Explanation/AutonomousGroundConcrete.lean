module

public import TruthCore.Explanation.AutonomousGroundNecessity
public import TruthCore.Causality.BruteFoundationBoundary

/-! Analyst finite comparison, attribution deferred. The target remains the
same rigid individual in the same ontology and supplied concrete designation.
The ground is a populated record containing only a nonexistential fact label;
this is not an account of own-nature essence or a real explanation. -/

@[expose] public section

namespace TruthCore.Explanation.AutonomousGroundConcrete
open TruthCore.Explanation.AutonomousGroundNecessity
open TruthCore.Explanation.ExistenceIngredient
open TruthCore.Explanation.PSRStrength
open TruthCore.Causality.JointGroups
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.German.Kant.CosmologicalInference

/-- Two complete alternatives, with rigid candidates false (the target) and
true (a contingent neighbour). Both are designated concrete for this modal
comparison; no concrete/abstract classification theorem is claimed. -/
def model : Profile Bool Bool where
  ontic := {
    frame := ⟨fun _ _ => True⟩
    ExistsAt := fun w b => b = false ∨ w = false
    Causes := fun _ _ _ => False
  }
  concrete := fun _ => True
  grounds := fun _ _ _ => False

/-- Positive labels track the SAME ontology; other labels hold throughout.
Essential labels are false: they are not silently made modal/essence truths.
No binary explanation or efficient-cause semantics is inferred from the record. -/
def arena : Arena Bool Bool (Fact Bool Unit) where
  ontic := model.ontic
  holds := fun w f => match f with
    | .inl (.fact b) => model.ontic.ExistsAt w b
    | .inr (.inl _) => False
    | .inr (.inr _) => True
  exist := positive
  explains := fun _ _ _ => False
  conjunct := fun _ _ => False

/-- One admitted full record, populated by a single other-fact contributor.
The enabler list is empty; its union with contributors is still retained. -/
def ground : Groups (Fact Bool Unit) Unit where
  contributors := fun _ => {other ()}
  enablers := fun _ => ∅
  effect := fun _ => positive false
  admitted := fun _ => True

def autonomous (f : Fact Bool Unit) : Prop := f = other ()

/-- Full five-input package AND necessary concrete endpoint AND failure of
IngredientAt, on one fixed model. Additional conjuncts certify nonempty grounds,
actual contingent concrete presence, and population at every world. The target
is necessary; the neighbour is contingent, so universal collapse is not claimed. -/
def Certificate : Prop :=
  ActualConcreteTargetAt arena model.concrete false false ∧
  AutonomousFullGround ground autonomous false ∧
  AutonomousFactsNecessaryAt arena autonomous false ∧
  WholeGroundNecessitatesTargetAt arena ground false false ∧
  PositiveTargetCoherent arena false ∧
  NecessaryConcreteAt model false ∧
  ¬ IngredientAt ground false ∧
  (∃ f, f ∈ ground.members ()) ∧
  (model.concrete true ∧ ContingentAt model.ontic false true) ∧
  (∀ w, InhabitedAt model w)

end TruthCore.Explanation.AutonomousGroundConcrete
