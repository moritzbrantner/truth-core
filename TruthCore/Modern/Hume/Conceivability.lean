import TruthCore.Isabelle.AFP.GoedelGod

/-! Issue #248 tests stronger reconstructions, not axioms attributed to Hume.
The verified witness is HUME-TREATISE-I-3-3, especially I.3.3 §3.
Reuse the Scott embedding's predicates/Box/Dia, but none of its theological axioms.
Full function quantification includes singleton predicates; world identity below
therefore uses separation explicitly. All claims are scoped to accessibility.
-/
namespace TruthCore.Modern.Hume.Conceivability
open TruthCore.Modal
open TruthCore.Isabelle.AFP.GoedelGod (MProp Box Dia)
universe u

abbrev Conception (W : Type u) := MProp W → MProp W

def StrongBridge {W : Type u} (F : Frame W) (C : Conception W) : MProp W :=
  fun w => ∀ P, C P w → Dia F P w

def Collapse {W : Type u} (F : Frame W) : MProp W :=
  fun w => ∀ P : MProp W, P w → Box F P w

def Contingent {W : Type u} (F : Frame W) (P : MProp W) (w : W) : Prop :=
  Dia F P w ∧ Dia F (fun v => ¬ P v) w

/-- A deliberately bounded representation of the §3 conclusion: reasoning
from mere ideas does not refute the description of an uncaused beginning.
`refutes` is an explicit interpretation parameter, not Lean provability and
not metaphysical impossibility. The source claim leaves its adequacy open. -/
def NarrowWithholding {D : Type u} (refutes : D → Prop) (uncausedBeginning : D) : Prop :=
  ¬ refutes uncausedBeginning

/-- Two distinct alternatives. Their modal interpretation is stipulated. -/
def universal : Frame Bool := ⟨fun _ _ => True⟩

/-- A reflexive, transitive branching frame; false sees both, true only itself. -/
def branching : Frame Bool := ⟨fun w v => w = false ∨ v = true⟩

/-- H is true at false, false at true; conceiving ¬H at false remains consistent. -/
def selfC : Conception Bool :=
  fun P w => (w = false ∧ P true) ∨ w = true

/-- A counterexample with a universally conceivable impossible proposition. -/
def indiscriminate : Conception Bool := fun _ _ => True

def SelfApplicationLaw : Prop :=
  ∀ (W : Type) (F : Frame W) (C : Conception W) w,
    StrongBridge F C w → C (fun v => ¬ StrongBridge F C v) w →
      Dia F (fun v => ¬ StrongBridge F C v) w

def NecessaryConflictLaw : Prop :=
  ∀ (W : Type) (F : Frame W) (C : Conception W) w,
    StrongBridge F C w → C (fun v => ¬ StrongBridge F C v) w →
      ¬ Box F (StrongBridge F C) w

/-- Full comprehension supplies the identity predicate P(v) := v = w. -/
def SeparationLaw : Prop :=
  ∀ (W : Type) (F : Frame W) w, Collapse F w →
    ∀ v, F.access w v → v = w

def ComponentLaw : Prop :=
  ∀ (W : Type) (F : Frame W), Symmetric F → Transitive F →
    ∀ w, Dia F (Collapse F) w → Collapse F w

def ContingencyObstructionLaw : Prop :=
  ∀ (W : Type) (F : Frame W), Symmetric F → Transitive F →
    ∀ w (P : MProp W), Contingent F P w → ¬ Dia F (Collapse F) w

/-- Conditional reductio: the unrestricted bridge and C(MC) cannot coexist
with independently warranted contingency on a symmetric transitive component. -/
def CollapseConceptionLaw : Prop :=
  ∀ (W : Type) (F : Frame W) (C : Conception W),
    Symmetric F → Transitive F → ∀ w (P : MProp W),
      Contingent F P w → StrongBridge F C w → ¬ C (Collapse F) w

/-- All advertised tests, not a refutation of Hume or a real-world contingency claim. -/
def Checks : Prop :=
  SelfApplicationLaw ∧ NecessaryConflictLaw ∧ SeparationLaw ∧ ComponentLaw ∧
  ContingencyObstructionLaw ∧ CollapseConceptionLaw ∧
  (¬ StrongBridge universal indiscriminate false) ∧
  (StrongBridge universal selfC false ∧
    selfC (fun v => ¬ StrongBridge universal selfC v) false) ∧
  (Contingent universal (fun w => w = true) false) ∧
  (Reflexive branching ∧ Transitive branching ∧
    Dia branching (Collapse branching) false ∧ ¬ Collapse branching false) ∧
  (NarrowWithholding (fun _ : Unit => False) () ∧
    StrongBridge universal (fun _ _ => False) false) ∧
  (Collapse (⟨fun w v : Bool => w = v⟩ : Frame Bool) false ∧
    (false : Bool) ≠ true)
end TruthCore.Modern.Hume.Conceivability
