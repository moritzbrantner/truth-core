import TruthCore.Causality.ScopedActualCausality
import Mathlib.Order.Sum.Order

/-! OPEN analyst restriction of atomic-part existence to actual CONTINGENT
objects. Necessary individuals need not have simple parts. Same Ontic,
actual-node order and frame-relative necessity as the scoped route.
The disjoint-sum controls are formal scope tests, not explanations of an
infinite causal regress, source claims or metaphysically possible worlds. -/
namespace TruthCore.Causality.ContingentAtomicity
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Causality.WorldSourceRegress
open TruthCore.Causality.AtomisticCausalSource
open TruthCore.Causality.ScopedActualCausality

def ContingentAtomicParts {W B : Type} (m : Ontic W B) (w : W)
    [PartialOrder (Actual m w)] : Prop :=
  ∀ x : Actual m w, ContingentAt m w x.val →
    ∃ a : Actual m w, a ≤ x ∧ IsMin a

namespace Controls
/-- Standard disjoint sum, not a linear/lexicographic sum. The right component
is the existing reversed-Nat atomless order, with successors as strict parts. -/
abbrev Carrier := Unit ⊕ OrderDual Nat
def point : Carrier := .inl ()
def gunk (n : Nat) : Carrier := .inr (OrderDual.toDual n)

def strict : Ontic Bool Carrier where
  frame := ⟨fun _ _ => True⟩
  ExistsAt := fun w x => w = false ∨ match x with
    | .inl _ => False
    | .inr _ => True
  Causes := fun w c e => w = false ∧ c = gunk 0 ∧ e = point

def reverse : Ontic Bool Carrier where
  frame := ⟨fun _ _ => True⟩
  ExistsAt := fun w x => w = false ∨ match x with
    | .inl _ => True
    | .inr _ => False
  Causes := fun w c e => w = false ∧ c = point ∧ e ≠ point

/-- Both selected actual carriers inherit the SAME standard disjoint order. -/
def strictNode (x : Carrier) : Actual strict false := ⟨x, Or.inl rfl⟩
def reverseNode (x : Carrier) : Actual reverse false := ⟨x, Or.inl rfl⟩
end Controls

/-- First model: new atomicity holds but old atomicity fails, with nonvacuous
contingent point/caused-simple singleton/cover. Second: NE holds alongside
contingent atomless objects, so NE does not imply the new premise, even under
the other structural and causal inputs. Its caused-simple family is empty and
its conditional cover vacuous. No finite atomlessness claim is made. -/
def Control : Prop :=
  ObjectPopulation (Actual Controls.strict false) ∧
  ConditionalCausedSimpleCover (actualGraph Controls.strict false) ∧
  CauseEffectNonoverlap (actualGraph Controls.strict false) ∧
  SelectedActualCausalCoverage Controls.strict false ∧
  ContingentAtomicParts Controls.strict false ∧
  ¬ AtomicParts (Actual Controls.strict false) ∧
  ContingentAt Controls.strict false Controls.point ∧
  NecessaryBeing Controls.strict false ∧
  (∀ a : Actual Controls.strict false,
    CausedSimples (actualGraph Controls.strict false) a ↔ a.val = Controls.point) ∧
  ObjectPopulation (Actual Controls.reverse false) ∧
  ConditionalCausedSimpleCover (actualGraph Controls.reverse false) ∧
  CauseEffectNonoverlap (actualGraph Controls.reverse false) ∧
  SelectedActualCausalCoverage Controls.reverse false ∧
  ¬ ContingentAtomicParts Controls.reverse false ∧
  ContingentAt Controls.reverse false (Controls.gunk 0) ∧
  NecessaryBeing Controls.reverse false ∧
  (∀ a : Actual Controls.reverse false,
    ¬ CausedSimples (actualGraph Controls.reverse false) a)

end TruthCore.Causality.ContingentAtomicity
