module

public import TruthCore.Causality.CausalMapsBatch1

/-! Analyst reconstruction, attribution deferred. `C` is one fixed context:
respect, event, clock and world must be included in that same index by a client.
`Integrated x p q c` is an OPEN primitive: p's moving q constitutes x's exercise
of self-motion, rather than merely occurring inside x at the same time.
No structural axiom or applicability to actual animals is asserted. -/
@[expose] public section
namespace TruthCore.Causality.SelfMotionSeparation
universe u v

/-- Diagonal motion: the mover and moved are numerically the same. -/
structure Diagonal {B : Type u} {C : Type v}
    (Moves : B → B → C → Prop) (x : B) (c : C) : Prop where
  moves : Moves x x c

/-- Whole/parts reconstruction: a moving whole exercises self-motion through
one proper part moving a different proper part. Whole motion and integration
are required; coincident internal motion alone is insufficient. -/
structure WholeParts {B : Type u} {C : Type v}
    (Part : B → B → Prop) (Moves : B → B → C → Prop)
    (Moved : B → C → Prop) (Integrated : B → B → B → C → Prop)
    (x : B) (c : C) : Prop where
  whole_moved : Moved x c
  parts : ∃ p q, Part p x ∧ p ≠ x ∧ Part q x ∧ q ≠ x ∧ p ≠ q ∧
    Moves p q c ∧ Integrated x p q c

/-- Explicit OPEN bridge from diagonal motion to the whole/parts reconstruction.
No bridge in either direction is implicit. -/
def DiagonalHasWholeParts {B : Type u} {C : Type v}
    (Part : B → B → Prop) (Moves : B → B → C → Prop)
    (Moved : B → C → Prop) (Integrated : B → B → B → C → Prop) : Prop :=
  ∀ x c, Diagonal Moves x c → WholeParts Part Moves Moved Integrated x c

/-- OPEN bridge, restricted to integrated motion of proper distinct parts.
It transfers the same mover p and context c from p→q to p→whole. -/
def InternalMoverMovesWhole {B : Type u} {C : Type v}
    (Part : B → B → Prop) (Moves : B → B → C → Prop)
    (Integrated : B → B → B → C → Prop) : Prop :=
  ∀ x p q c, Part p x → p ≠ x → Part q x → q ≠ x → p ≠ q →
    Moves p q c → Integrated x p q c → Moves p x c

namespace Control
inductive Obj where | whole | motor | limb deriving DecidableEq
open Obj
/-- Integral proper parts of the one selected whole. -/
def Part (p x : Obj) : Prop := x = whole ∧ (p = motor ∨ p = limb)
def Moved (x : Obj) (_ : Unit) : Prop := x = whole
/-- Integration is explicit even in the finite witness. -/
def Integrated (x p q : Obj) (_ : Unit) : Prop :=
  x = whole ∧ p = motor ∧ q = limb
/-- Internal motion, without either p→whole or whole→whole. -/
def Internal (p q : Obj) (_ : Unit) : Prop := p = motor ∧ q = limb
/-- Add the part-to-whole edge, still without diagonal motion. -/
def Lifted (p q : Obj) (_ : Unit) : Prop := p = motor ∧ (q = limb ∨ q = whole)
/-- Internal and diagonal events, without part-to-whole motion. -/
def Joined (p q : Obj) (c : Unit) : Prop :=
  Internal p q c ∨ (p = whole ∧ q = whole)
/-- Joint nonvacuity witness includes all three distinct edges. -/
def Full (p q : Obj) (c : Unit) : Prop := Joined p q c ∨ (p = motor ∧ q = whole)
/-- A diagonal event with no internal or part-to-whole edge. -/
def OnlyDiagonal (p q : Obj) (_ : Unit) : Prop := p = whole ∧ q = whole

/-- Populated witnesses discriminate internal, whole and diagonal motion.
Each sufficient bridge has a separate omission model; Full supplies joint nonvacuity.
No witness is a claim about the real world. -/
def Certificate : Prop :=
  (WholeParts Part Internal Moved Integrated whole () ∧
    ¬ Diagonal Internal whole () ∧ ¬ (∃ p, Part p whole ∧ Internal p whole ())) ∧
  (WholeParts Part Lifted Moved Integrated whole () ∧
    ¬ Diagonal Lifted whole () ∧ Lifted motor whole ()) ∧
  (Diagonal OnlyDiagonal whole () ∧
    InternalMoverMovesWhole Part OnlyDiagonal Integrated ∧
    ¬ WholeParts Part OnlyDiagonal Moved Integrated whole () ∧
    ¬ TruthCore.Causality.CausalMapsBatch1.SelfMoverMovesByADistinctPart OnlyDiagonal Part) ∧
  (DiagonalHasWholeParts Part Joined Moved Integrated ∧
    ¬ TruthCore.Causality.CausalMapsBatch1.SelfMoverMovesByADistinctPart Joined Part) ∧
  (DiagonalHasWholeParts Part Full Moved Integrated ∧
    InternalMoverMovesWhole Part Full Integrated ∧ Diagonal Full whole ()) ∧
  (¬ WholeParts Part Internal (fun _ _ => False) Integrated whole ()) ∧
  (¬ WholeParts Part Internal Moved (fun _ _ _ _ => False) whole ())
end Control
end TruthCore.Causality.SelfMotionSeparation
