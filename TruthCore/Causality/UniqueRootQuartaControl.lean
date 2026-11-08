module
public import TruthCore.Causality.DirectEsseRootPerfectionGoodness
@[expose] public section
namespace TruthCore.Causality.UniqueRootQuartaControl
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryRootFork
open TruthCore.Causality.CogitoNecessaryConcrete
open TruthCore.Causality.DirectEsseRootPerfectionGoodness
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Latin.Aquinas.SummaTheologiae
/-- Only false is concrete; both candidates exist. This tests formal
consequence, not an actual metaphysical interpretation. -/
def model : Profile Unit Bool where
  ontic := { frame := { access := fun _ _ => True }, ExistsAt := fun _ _ => True,
             Causes := fun _ _ _ => False }
  concrete := fun x => x = false
  grounds := fun _ _ _ => False
def act : Bool → Unit → Prop := fun _ _ => True
def more : Unit → Bool → Bool → Prop := fun _ _ _ => False
def cause : Bool → Bool → Unit → Prop := fun x y _ => x ≠ y
def package : Prop := NecessaryPerfectRootAt model () act more ()
theorem packageHolds : package := by
  refine ⟨false, ⟨⟨rfl, trivial⟩, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro y h; exact h.2.2
  · intro v hv; trivial
  · intro x hx; exact hx.1.1
  · exact ⟨trivial, fun _ h => h⟩
  · intro x r hx; trivial
/-- Populated causality in the positive witness; omission of genus retains
all root/perfection data but deletes every causal edge. Omitting the package
permits empty actuality while the genus implication holds vacuously. -/
def Certificate : Prop :=
  (package ∧ MaximumInBeingCausesAllBeingsReading act more cause () ∧
    MaximeEnsCausesBeingOfAllReading act more cause () ∧ cause false true ()) ∧
  (package ∧ ¬ MaximeEnsCausesBeingOfAllReading act more (fun _ _ _ => False) ()) ∧
  (MaximumInBeingCausesAllBeingsReading (fun (_ : Bool) (_ : Unit) => False) more cause () ∧
    ¬ MaximeEnsCausesBeingOfAllReading (fun (_ : Bool) (_ : Unit) => False) more cause ())
end TruthCore.Causality.UniqueRootQuartaControl
