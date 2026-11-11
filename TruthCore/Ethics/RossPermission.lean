module
public import TruthCore.Modal.DeonticFutureBoundary
@[expose] public section
namespace TruthCore.Ethics.RossPermission
open TruthCore.Modal TruthCore.Modal.DeonticFutureBoundary

/-- Ideal-compatible weak permission; neither available fulfillment nor issued authorization. -/
def Weak (i : Frame W) (w : W) (p : W → Prop) : Prop :=
  ∃ v, i.access w v ∧ p v

/-- Extensional neighborhood of explicitly issued contents. Membership is primitive input;
no closure, authority, feasibility or moral endorsement is asserted. -/
structure Norms (W : Type) where
  issued : (W → Prop) → Prop

/-- Strong permission here means membership among issued authorizations. -/
def Strong (n : Norms W) (p : W → Prop) : Prop := n.issued p

/-- Exact-content obligation rival. Even logically weaker contents need not be issued.
This extensional account does not distinguish logically equivalent presentations. -/
def ExactDuty (n : Norms W) (p : W → Prop) : Prop := n.issued p

inductive Action | mail | burn | keep deriving DecidableEq

def mail (a : Action) : Prop := a = .mail
def burn (a : Action) : Prop := a = .burn
def one : Frame Action := ⟨fun _ a => a = .mail⟩
def both : Frame Action := ⟨fun _ a => a = .mail ∨ a = .burn⟩
def issuedMail : Norms Action := ⟨fun p => ∀ a, p a ↔ mail a⟩
def issuedNone : Norms Action := ⟨fun _ => False⟩

/-- All logical quantification is over one selected ideal frame and point.
No availability, actual performance or moral authority occurs in this certificate. -/
def Certificate : Prop :=
  (∀ (W : Type) (i : Frame W) w (p q : W → Prop),
    Ought i w p → Ought i w (fun a => p a ∨ q a)) ∧
  (∀ (W : Type) (i : Frame W) w (p : W → Prop),
    Weak i w p ↔ ¬ Ought i w (fun a => ¬ p a)) ∧
  (∀ (W : Type) (i : Frame W) w (p q : W → Prop),
    Ought i w (fun a => p a ∨ q a) → ¬ Ought i w p → Weak i w q) ∧
  (∀ (W : Type) (i : Frame W) w (p q : W → Prop),
    Ought i w (fun a => p a ∨ q a) → ¬ Ought i w p → ¬ Ought i w q →
      Weak i w p ∧ Weak i w q) ∧
  (∀ (W : Type) (i : Frame W) w (p q : W → Prop),
    Ought i w (fun a => p a ∨ q a) →
    (∀ a, i.access w a → ¬ (p a ∧ q a)) →
      (Weak i w q ↔ ¬ Ought i w p) ∧ (Weak i w p ↔ ¬ Ought i w q)) ∧
  (Serial one ∧ Ought one .keep mail ∧
    Ought one .keep (fun a => mail a ∨ burn a) ∧ ¬ Weak one .keep burn) ∧
  (Serial both ∧ Ought both .keep (fun a => mail a ∨ burn a) ∧
    ¬ Ought both .keep mail ∧ ¬ Ought both .keep burn ∧
    Weak both .keep mail ∧ Weak both .keep burn ∧
    ¬ Strong issuedNone mail ∧ ¬ Strong issuedNone burn) ∧
  (Weak one .keep mail ∧ Ought one .keep mail ∧
    Ought one .keep (fun a => mail a ∨ mail a)) ∧
  (ExactDuty issuedMail mail ∧
    ¬ ExactDuty issuedMail (fun a => mail a ∨ burn a)) ∧
  (∀ (W : Type) (i : Frame W) w (p q : W → Prop) (n : Norms W),
    Weak i w p → Weak i w q →
    (∀ r, Weak i w r → Strong n r) → Strong n p ∧ Strong n q)
end TruthCore.Ethics.RossPermission
