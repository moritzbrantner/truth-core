module
public import TruthCore.Results.Causality.SelectedAncestry.Solution
public import TruthCore.Results.Causality.UniqueRootPerfection.Solution
@[expose] public section
namespace TruthCore.Causality.SelectedAncestryUniqueControl
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.SelectedAncestry
open TruthCore.Causality.NecessaryRootUniqueness
open TruthCore.Causality.NecessaryConcreteRouteBridge
open TruthCore.Causality.ExistenceActuality
open TruthCore.Causality.DirectEsseRootUniquenessAtBeing
open TruthCore.Latin.Aquinas.SummaTheologiae
/-- Finite formal interpretations only; neither represents a real metaphysical possibility. -/
def full : Profile Unit Bool where
  ontic := {frame := ⟨fun _ _ => True⟩, ExistsAt := fun _ _ => True, Causes := fun _ _ _ => False}
  concrete := fun _ => True
  grounds := fun _ _ _ => False
def empty : Profile Unit Bool where
  ontic := {frame := ⟨fun _ _ => True⟩, ExistsAt := fun _ _ => False, Causes := fun _ _ _ => False}
  concrete := fun _ => True
  grounds := fun _ _ _ => False
def positive : Profile Unit Unit where
  ontic := {frame := ⟨fun _ _ => True⟩, ExistsAt := fun _ _ => True, Causes := fun _ _ _ => False}
  concrete := fun _ => True
  grounds := fun _ _ _ => False
def act (b : Bool) : Bool → Unit → Prop := fun _ _ => b = true
def more (b : Bool) : Unit → Bool → Bool → Prop := fun _ _ _ => b = true
def cause (b : Bool) : Bool → Bool → Unit → Prop := fun x y _ => b = true ∧ x ≠ y
def policies (m : Profile Unit Bool) (a g c : Bool) : Prop :=
  MaximumInBeingCausesAllBeingsReading (act a) (more g) (cause c) () ∧
  ExistingInActAt m.ontic (act a) () () ∧
  EsseCauseIsActualConcreteGround m () (cause c) () ∧
  GradesToMaximumAtBeing (act a) (more g) ()
/-- One joint nonvacuity witness and omissions of each nonlogical carrying
premise. Excluded middle is retained as the theorem's explicit logical input;
no intuitionistic independence claim about it is made. -/
def Certificate : Prop :=
  NecessaryRootAncestor positive () () ∧
  MaximumInBeingCausesAllBeingsReading (fun (_ : Unit) (_ : Unit) => True)
    (fun _ _ _ => False) (fun _ _ _ => False) () ∧
  ExistingInActAt positive.ontic (fun _ (_ : Unit) => True) () () ∧
  EsseCauseIsActualConcreteGround positive () (fun _ _ (_ : Unit) => False) () ∧
  GradesToMaximumAtBeing (fun (_ : Unit) (_ : Unit) => True) (fun _ _ _ => False) () ∧
  NecessaryRootAncestor full () false ∧ ¬ UniqueNecessaryActualRootAt full () ∧
  (policies empty false false false ∧ ¬ NecessaryRootAncestor empty () false ∧
    ¬ UniqueNecessaryActualRootAt empty ()) ∧
  (ExistingInActAt full.ontic (act true) () () ∧
    EsseCauseIsActualConcreteGround full () (cause false) () ∧
    GradesToMaximumAtBeing (act true) (more false) ()) ∧
  (MaximumInBeingCausesAllBeingsReading (act false) (more false) (cause false) () ∧
    EsseCauseIsActualConcreteGround full () (cause false) () ∧
    GradesToMaximumAtBeing (act false) (more false) ()) ∧
  (MaximumInBeingCausesAllBeingsReading (act true) (more false) (cause true) () ∧
    ExistingInActAt full.ontic (act true) () () ∧
    GradesToMaximumAtBeing (act true) (more false) ()) ∧
  (MaximumInBeingCausesAllBeingsReading (act true) (more true) (cause false) () ∧
    ExistingInActAt full.ontic (act true) () () ∧
    EsseCauseIsActualConcreteGround full () (cause false) ())
end TruthCore.Causality.SelectedAncestryUniqueControl
