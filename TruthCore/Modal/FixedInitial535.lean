module
public import TruthCore.German.Kant.CosmologicalInference
public import Mathlib.Data.Fintype.Prod
@[expose] public section
namespace TruthCore.Modal.FixedInitial535
open TruthCore.German.Kant.CosmologicalInference
/-- Analyst profile. Initial is a selected roster, not a definition of temporal
firstness. Description and later are qualitative data; grounds is primitive
existential support. No chance, complete-history adequacy or naturalness follows. -/
structure History (W B D : Type) where
  ontic : Ontic W B
  initial : B → W → Prop
  description : W → D
  later : W → Bool
  grounds : W → B → B → Prop

def Rigid {W B D} (h : History W B D) (a : W) : Prop :=
  (∃ b, h.initial b a) ∧
  (∀ b w, h.initial b w → h.ontic.ExistsAt w b) ∧
  (∀ b w, h.ontic.frame.access a w → h.initial b a → h.initial b w)

def Propagation : Prop :=
  ∀ (W B D : Type) (h : History W B D) (a : W),
    Rigid h a → ∃ b, h.initial b a ∧ NecessaryAt h.ontic a b

def SameDescription {W B D} (h : History W B D) (a : W) : Prop :=
  ∀ w, h.ontic.frame.access a w → h.description w = h.description a

def LaterVariation {W B D} (h : History W B D) (a : W) : Prop :=
  ∃ w, h.ontic.frame.access a w ∧ h.later w ≠ h.later a

/-- Conditional origin preservation constrains origin only WHERE this bearer exists. -/
def ConditionalOrigin {W B D} (h : History W B D) (a : W) : Prop :=
  ∀ b w, h.initial b a → h.ontic.ExistsAt w b → h.initial b w

/-- All finite profiles share literal identity on Bool × Bool. First coordinate
is a tag; second is root/later role. The rotating root is not the rigid root. -/
def profile (rotate different dependent : Bool) : History Bool (Bool × Bool) Bool where
  ontic := {
    frame := { access := fun _ _ => True }
    ExistsAt := fun w b => if b.2 then b.1 = w else
      b.1 = (if rotate then w else false) ∨ dependent = true
    Causes := fun _ _ _ => False }
  initial := fun b w => b.2 = false ∧ b.1 = (if rotate then w else false)
  description := fun w => if different then w else false
  later := fun w => w
  grounds := fun _ s t => dependent = true ∧ s = (true, false) ∧ t = (false, false)

def Joint (rotate different dependent : Bool) : Prop :=
  let h := profile rotate different dependent
  (∀ w, ∃ b, h.initial b w ∧ h.ontic.ExistsAt w b) ∧
  LaterVariation h false ∧ ConditionalOrigin h false ∧
  (∀ w s t, h.grounds w s t →
    h.ontic.ExistsAt w s ∧ h.ontic.ExistsAt w t ∧ s ≠ t)

def RigidBranch : Prop :=
  (Joint false false false ∧ Rigid (profile false false false) false ∧
    SameDescription (profile false false false) false ∧
    NecessaryAt (profile false false false).ontic false (false, false))

def Controls : Prop :=
  RigidBranch ∧
  (Joint true false false ∧ SameDescription (profile true false false) false ∧
    ¬ NecessaryBeing (profile true false false).ontic false ∧
    ¬ Rigid (profile true false false) false) ∧
  (Joint true true false ∧ ¬ SameDescription (profile true true false) false ∧
    ¬ NecessaryBeing (profile true true false).ontic false) ∧
  (Joint false false true ∧ Rigid (profile false false true) false ∧
    NecessaryAt (profile false false true).ontic false (false, false) ∧
    ∀ w, (profile false false true).grounds w (true, false) (false, false))
end TruthCore.Modal.FixedInitial535
