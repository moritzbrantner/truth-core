import TruthCore.Modal.NecessaryIfExistent
import TruthCore.Modal.GraphBridge

/-! Exact pointwise frame correspondence for #437. Mathematical reachability
uses Mathlib Relation.ReflTransGen, rather than a new modal or graph engine.
The input is still the boxed conditional at a single named standpoint; no
metaphysical adequacy or possibility premise is established. -/
namespace TruthCore.Modal.NecessaryIfConnectivity
open TruthCore.Modal.NecessaryIfExistent
open TruthCore.Isabelle.AFP.GoedelGod (Box Dia)
universe u
variable {W : Type u}

/-- A step must start in the standpoint's successor set. Its target may lie
outside that set; such an exit cannot be followed by another masked step.
This source guard matches exactly the scope of □(G → □G). -/
def maskedStep (F : Frame W) (w : W) (a b : W) : Prop :=
  F.access w a ∧ F.access a b

/-- Every ordered pair of successors is connected by a finite masked path.
Length zero is permitted. Empty and singleton successor sets are covered;
there is no existence, seriality, reflexivity or actual-truth assumption. -/
def SuccessorConnected (F : Frame W) (w : W) : Prop :=
  ∀ a b, F.access w a → F.access w b →
    Relation.ReflTransGen (maskedStep F w) a b

/-- Validity of the forward conditional over all world predicates, at w. -/
def ForwardAt (F : Frame W) (w : W) : Prop :=
  ∀ G : W → Prop, NecessaryIf F G w → Dia F G w → Box F G w

/-- Three worlds forming a reflexive symmetric line, with none at the center.
The two leaves lack a direct edge to one another. -/
def line : Frame (Option Bool) :=
  ⟨fun a b => a = b ∨ a = none ∨ b = none⟩

/-- Exact correspondence, familiar sufficient conditions, and a concrete
strictness witness. No minimal global modal-logic classification is asserted. -/
def Certificate : Prop :=
  (∀ (W : Type) (F : Frame W) (w : W),
    ForwardAt F w ↔ SuccessorConnected F w) ∧
  (∀ (W : Type) (F : Frame W) (w : W),
    Euclidean F → SuccessorConnected F w) ∧
  (∀ (W : Type) (F : Frame W) (w : W),
    Reflexive F → Symmetric F → SuccessorConnected F w) ∧
  (Reflexive line ∧ Symmetric line ∧
    (∀ w, SuccessorConnected line w) ∧ ¬ Euclidean line)
end TruthCore.Modal.NecessaryIfConnectivity
