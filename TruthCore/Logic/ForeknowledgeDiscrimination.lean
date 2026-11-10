module
public import TruthCore.Logic.JustificationIntrospection
/-! Selected-content relational diagnostic for #1380. Analyst formulation,
attribution deferred; neither an account of divine cognition nor free agency. -/
@[expose] public section
namespace TruthCore.Logic.ForeknowledgeDiscrimination
open TruthCore.Modal
open TruthCore.Logic.JustificationIntrospection
/-- Agreement on a supplied admissible family; no totality of all truths. -/
def TruthClass {W : Type} (C : (W → Bool) → Prop) (w v : W) : Prop :=
  ∀ p, C p → p v = p w
/-- Knowing each selected content or its negation, according to its truth. -/
def Complete {W : Type} (E : Frame W) (C : (W → Bool) → Prop) (w : W) : Prop :=
  ∀ p, C p → (p w = true → Knows E (fun v => p v = true) w) ∧
    (p w = false → Knows E (fun v => p v = false) w)
/-- Open interpretation, applicable equally to intrinsic states or hard-past
projections. It is not entailed by temporal immutability or necessity. -/
def Supervenes {W S : Type} (E : Frame W) (I : W → S) : Prop :=
  ∀ u v, I u = I v → ∀ x, E.access u x ↔ E.access v x
/-- Selected-family equivalence and factive discrimination. -/
def Core : Prop :=
  (∀ (W : Type) (E : Frame W) C w,
    Complete E C w ↔ ∀ v, E.access w v → TruthClass C w v) ∧
  (∀ (W : Type) (E : Frame W) C u v,
    E.access u u → E.access v v → Complete E C u → Complete E C v →
    (∃ p, C p ∧ p u ≠ p v) → ¬ (∀ x, E.access u x ↔ E.access v x)) ∧
  (∀ (W S : Type) (E : Frame W) C (I : W → S) u v,
    Supervenes E I → I u = I v → E.access u u → E.access v v →
    Complete E C u → Complete E C v → (∃ p, C p ∧ p u ≠ p v) → False)
/-- Canonical equivalence relation on the selected profiles. -/
def canonical {W : Type} (C : (W → Bool) → Prop) : Frame W := ⟨TruthClass C⟩
/-- Two Boolean coordinates: necessary-only, one independent bit, both bits. -/
def profile (n : Nat) (u v : Bool × Bool) : Prop :=
  if n = 0 then True else if n = 1 then u.1 = v.1 else u = v
/-- Explicit bounded count via the four representatives, rather than all-world
minimality. The general discrimination theorem supplies the lower bound. -/
def classes (n : Nat) : List (Bool × Bool) :=
  if n = 0 then [(false,false)] else if n = 1 then [(false,false),(true,false)]
  else [(false,false),(false,true),(true,false),(true,true)]
def Controls : Prop :=
  (∀ w : Bool, Complete ⟨fun u v => u = v⟩ (fun p => p = id) w) ∧
  (¬ Complete (⟨fun _ _ : Bool => True⟩) (fun p => p = id) false) ∧
  (∀ w : Bool, Complete ⟨fun _ _ => False⟩ (fun p => p = id) w) ∧
  (∀ w : Bool, Complete ⟨fun _ _ => True⟩ (fun p => p = fun _ => true) w) ∧
  (∀ n : Fin 3, ∀ w : Bool × Bool, ∃ r ∈ classes n.val, profile n.val w r) ∧
  (∀ n : Fin 3, ∀ u ∈ classes n.val, ∀ v ∈ classes n.val, profile n.val u v → u = v) ∧
  ((classes 0).length = 1 ∧ (classes 1).length = 2 ∧ (classes 2).length = 4)
/-- Coordinate families for the finite profile controls. -/
def family (n : Nat) (p : (Bool × Bool) → Bool) : Prop :=
  if n = 0 then p = (fun _ => true) else if n = 1 then p = Prod.fst
  else p = Prod.fst ∨ p = Prod.snd
/-- The explicitly counted relations are precisely selected truth classes. -/
def FiniteProfiles : Prop :=
  ∀ n : Fin 3, ∀ u v : Bool × Bool, TruthClass (family n.val) u v ↔ profile n.val u v
/-- The canonical model is factive, symmetric, transitive and complete, and
its rows coincide exactly when the selected profiles coincide. -/
def CanonicalCertificate : Prop :=
  ∀ (W : Type) C,
    Reflexive (canonical (W := W) C) ∧ Symmetric (canonical C) ∧
    Transitive (canonical C) ∧ (∀ w, Complete (canonical C) C w) ∧
    (∀ u v, TruthClass C u v ↔
      ∀ x, (canonical C).access u x ↔ (canonical C).access v x)
end TruthCore.Logic.ForeknowledgeDiscrimination
