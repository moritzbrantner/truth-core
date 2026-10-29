/- Checked two-point separators and structural extraction fixtures; no corpus claims. -/
import Lean
namespace TruthCore.InspectorFixture

def forward (P : Bool → Bool → Prop) (a b : Bool) : Prop := P a b
def reverse (P : Bool → Bool → Prop) (a b : Bool) : Prop := P b a
def shared (P Q : Bool → Prop) : Prop := ∃ x, P x ∧ Q x
def separate (P Q : Bool → Prop) : Prop := (∃ x, P x) ∧ (∃ x, Q x)
def alternating (R : Bool → Bool → Prop) : Prop := ∀ x, ∃ y, R x y
def uniform (R : Bool → Bool → Prop) : Prop := ∃ y, ∀ x, R x y
def grouped (P Q R : Prop) : Prop := (P ∧ Q) ∨ R
def groupedOther (P Q R : Prop) : Prop := P ∧ (Q ∨ R)
def equivalence (P Q : Prop) : Prop := P ↔ ¬ Q
structure LawfulRelation where
  relation : Bool → Bool → Prop
  reflexive : ∀ x, relation x x
def model (m : LawfulRelation) : Prop := m.relation false true

example : separate (· = false) (· = true) ∧ ¬ shared (· = false) (· = true) := by
  constructor
  · exact ⟨⟨false, rfl⟩, ⟨true, rfl⟩⟩
  · rintro ⟨x, hx, hy⟩
    cases hx
    cases hy

example : alternating (· = ·) ∧ ¬ uniform (· = ·) := by
  constructor
  · intro x; exact ⟨x, rfl⟩
  · rintro ⟨y, h⟩
    have h0 := h false
    have h1 := h true
    cases y <;> contradiction

example : forward (fun x y => x = false ∧ y = true) false true ∧
    ¬ reverse (fun x y => x = false ∧ y = true) false true := by
  exact ⟨⟨rfl, rfl⟩, fun h => Bool.noConfusion h.1⟩
end TruthCore.InspectorFixture
