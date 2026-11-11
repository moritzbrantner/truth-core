module
public import TruthCore.Ethics.RossPermission
@[expose] public section
namespace TruthCore.Ethics.RossDerived
open TruthCore.Ethics.RossPermission

/-- Consequence of ONE issued predicate, not a conjunction of the issued code.
Issuance is input; this definition supplies no authority or adequate compliance. -/
def Derived (n : Norms W) (q : W → Prop) : Prop :=
  ∃ p, n.issued p ∧ ∀ a, p a → q a

/-- Individually satisfiable mail and burn contents, without aggregation. -/
def issuedPair : Norms Action :=
  ⟨fun p => (∀ a, p a ↔ mail a) ∨ (∀ a, p a ↔ burn a)⟩
def issuedImpossible : Norms Action := ⟨fun p => ∀ a, p a ↔ False⟩

def Certificate : Prop :=
  (∀ (W : Type) (n : Norms W) p, n.issued p → Derived n p) ∧
  (∀ (W : Type) (n : Norms W) (p q : W → Prop),
    (∀ a, p a ↔ q a) → (Derived n p ↔ Derived n q)) ∧
  (∀ (W : Type) (n : Norms W) (p q : W → Prop),
    Derived n p → (∀ a, p a → q a) → Derived n q) ∧
  (∀ q, Derived issuedMail q ↔ q .mail) ∧
  (∀ q, ¬ Derived issuedNone q) ∧
  (∀ q, Derived issuedImpossible q) ∧
  (Derived issuedMail (fun a => mail a ∨ burn a) ∧
    ¬ Derived issuedMail burn) ∧
  ((∀ p, issuedPair.issued p → ∃ a, p a) ∧
    ¬ (∃ a, ∀ p, issuedPair.issued p → p a) ∧
    Derived issuedPair mail ∧ Derived issuedPair burn ∧
    ¬ Derived issuedPair (fun a => mail a ∧ burn a) ∧
    ¬ Derived issuedPair (fun _ => False))
end TruthCore.Ethics.RossDerived
