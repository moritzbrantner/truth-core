import TruthCore.German.Kant.CosmologicalInference
import TruthCore.Results.Modal.PossibilityTransfer.Solution

/-! Partial, relational designation: no name denotes merely because it occurs.
This is an analyst's profile, not an attribution to Kripke. The modal carrier
contains candidate descriptions; epistemic alternatives may vary reference.
Numerical identity uses Lean equality, not counterpart correspondence. -/
namespace TruthCore.Modal.RigidDesignation
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Isabelle.AFP.GoedelGod (Box)
open TruthCore.Modal.PossibilityTransfer (IncludedAt)
abbrev Name (W B : Type) := W → B → Prop

/-- On admitted successors, exactly the selected bearer is designated, precisely
when that bearer exists. No actual referent or necessary existence is asserted. -/
def RigidAt (m : Ontic W B) (n : Name W B) (w : W) (x : B) : Prop :=
  ∀ v, m.frame.access w v → ∀ y, n v y ↔ y = x ∧ m.ExistsAt v x

/-- Strict identity of two partial names requires a common existing denotation;
both names being empty does not make this proposition true. -/
def CoRef (a b : Name W B) (v : W) : Prop := ∃ x, a v x ∧ b v x

/-- Universally quantified conditional consequence, with actual co-reference
explicit and existence separated from conditional identity. The final clause
reuses the exact sufficient accessibility bridge from the two-relation result. -/
def Laws : Prop := ∀ (W B : Type) (m : Ontic W B) (E : TruthCore.Modal.Frame W)
    (a b : Name W B) w x,
  a w x → b w x → RigidAt m a w x → RigidAt m b w x →
  (Box m.frame (CoRef a b) w ↔ NecessaryAt m w x) ∧
  (∀ v, m.frame.access w v → m.ExistsAt v x → CoRef a b v) ∧
  (IncludedAt E m.frame w → NecessaryAt m w x → Box E (CoRef a b) w)

def disappearing : Ontic Bool Bool where
  frame := ⟨fun _ _ => True⟩
  ExistsAt := fun w x => w = false ∧ x = false
  Causes := fun _ _ _ => False

def absentName : Name Bool Bool := disappearing.ExistsAt

def epistemicModel : Ontic Bool Bool where
  frame := ⟨fun w v => v = w⟩
  ExistsAt := fun _ _ => True
  Causes := fun _ _ _ => False

def leftName : Name Bool Bool := fun _ x => x = false
def rightName : Name Bool Bool := fun w x => x = w
def E : TruthCore.Modal.Frame Bool := ⟨fun _ _ => True⟩

/-- Two reflexive finite controls with populated origins. First: actual co-reference and
rigidity permit shared nonexistence, defeating strict necessary co-reference.
Second: actual co-reference, M-rigidity and strict M-necessity coexist with
E-accessible nonidentity; both candidate bearers exist at both descriptions.
These are admissibility profiles, not claims about actual human knowledge. -/
def Controls : Prop :=
  (CoRef absentName absentName false ∧
    RigidAt disappearing absentName false false ∧
    ¬ Box disappearing.frame (CoRef absentName absentName) false) ∧
  (CoRef leftName rightName false ∧
    RigidAt epistemicModel leftName false false ∧
    RigidAt epistemicModel rightName false false ∧
    Box epistemicModel.frame (CoRef leftName rightName) false ∧
    ¬ Box E (CoRef leftName rightName) false ∧
    ¬ IncludedAt E epistemicModel.frame false)

def Checks : Prop := Laws ∧ Controls
end TruthCore.Modal.RigidDesignation
