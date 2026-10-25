import TruthCore.Modal.KResearch
import TruthCore.Modal.Cube

/-! Stipulated S4 experiments for #265, not a historical attribution.
The same fixed language is compared with all predicates; neither denotes
metaphysical possibility without a separate interpretation. -/
namespace TruthCore.Modal.S4Research
open TruthCore.Modal.ResearchFixture
open TruthCore.Modal.ResearchFinite
open TruthCore.Modal.KResearch (PossibilityActuality)
open TruthCore.Isabelle.AFP.GoedelGod (MProp Box Dia)
open TruthCore.Modern.Hume.Conceivability (Contingent)

/-- Mutual accessibility defines membership in the same cluster. -/
def SameCluster {W : Type} (F : Frame W) (w v : W) : Prop :=
  F.access w v ∧ F.access v w

/-- All hypotheses are inside the quantified mathematical result. Full collapse
forces at most one mutually accessible world; reflexivity supplies self-membership
and hence a singleton cluster. Terminality alone does not. Symmetry supplies the
backward edge absent from general S4 frames. -/
def Laws : Prop :=
  (∀ (W : Type) (F : Frame W) w,
    Reflexive F → (MC F allPredicates w ↔ Box F (MC F allPredicates) w)) ∧
  (∀ (W : Type) (F : Frame W) w v,
    MC F allPredicates w → SameCluster F w v → v = w) ∧
  (∀ (W : Type) (F : Frame W) w,
    Symmetric F → Dia F (MC F allPredicates) w → MC F allPredicates w)

inductive World where
  | root | left | right | twin
  deriving DecidableEq, Repr

/-- Root sees all worlds. Left is an isolated terminal singleton. When paired is
true, right and twin form a closed two-world cluster; otherwise each is a terminal
singleton. Atom false marks left; atom true marks twin only when unpaired. -/
def pockets (paired : Bool) : Model World Bool where
  worlds := [.root, .left, .right, .twin]
  complete := by
    intro w
    cases w with
    | root => exact .head _
    | left => exact .tail _ (.head _)
    | right => exact .tail _ (.tail _ (.head _))
    | twin => exact .tail _ (.tail _ (.tail _ (.head _)))
  edge := fun w => match w with
    | .root => fun _ => true
    | .left => fun v => match v with
      | .root => false
      | .left => true
      | .right => false
      | .twin => false
    | .right => fun v => match v with
      | .root => false
      | .left => false
      | .right => true
      | .twin => paired
    | .twin => fun v => match v with
      | .root => false
      | .left => false
      | .right => paired
      | .twin => true
  atom := fun w a => match w with
    | .root => false
    | .left => !a
    | .right => false
    | .twin => a && !paired

def language (paired : Bool) : Domain World :=
  expressible (pockets paired).frame (pockets paired).valuation

def p (w : World) : Prop := (pockets true).atom w false = true

/-- Branching persists in both domains even with an accessible collapsed singleton.
The frame also fails symmetry and Euclideanness, so S5 has not been assumed. -/
def Countermodels : Prop :=
  ∀ paired : Bool,
    FrameSatisfies .S4 (pockets paired).frame ∧
    (¬ Symmetric (pockets paired).frame) ∧
    (¬ Euclidean (pockets paired).frame) ∧
    MC (pockets paired).frame allPredicates .left ∧
    MC (pockets paired).frame (language paired) .left ∧
    Dia (pockets paired).frame (MC (pockets paired).frame allPredicates) .root ∧
    Dia (pockets paired).frame (MC (pockets paired).frame (language paired)) .root ∧
    (¬ MC (pockets paired).frame allPredicates .root) ∧
    (¬ MC (pockets paired).frame (language paired) .root) ∧
    (¬ Box (pockets paired).frame (MC (pockets paired).frame allPredicates) .root) ∧
    (¬ Box (pockets paired).frame (MC (pockets paired).frame (language paired)) .root) ∧
    Contingent (pockets paired).frame p .root ∧
    (¬ PossibilityActuality (pockets paired).frame allPredicates .root) ∧
    (¬ PossibilityActuality (pockets paired).frame (language paired) .root)

/-- A terminal pair is language-collapsed but not fully collapsed. Thus the
stronger possible-collapse → necessary-possible-collapse inference also fails
in S4 at full scope, although it holds in this particular restricted model. -/
def ScopeBoundary : Prop :=
  SameCluster (pockets true).frame .right .twin ∧
  World.right ≠ World.twin ∧
  (¬ MC (pockets true).frame allPredicates .right) ∧
  MC (pockets true).frame (language true) .right ∧
  MC (pockets true).frame (language true) .twin ∧
  (¬ Box (pockets true).frame (fun w => Dia (pockets true).frame
    (MC (pockets true).frame allPredicates) w) .root) ∧
  Box (pockets true).frame (fun w => Dia (pockets true).frame
    (MC (pockets true).frame (language true)) w) .root ∧
  (¬ PropositionalExtensionality (language true)) ∧
  eval (pockets true) .root (.diamond (.atom false)) = true ∧
  eval (pockets true) .root (.diamond (.neg (.atom false))) = true ∧
  witnesses (pockets true) .root (.atom false) = [.left] ∧
  counterexamples (pockets true) .root (.atom false) = [.root, .right, .twin]

/-- Unpaired terminal singletons retain branching while the fixed language
separates every label. Thus the counterexample to possible → actual collapse
survives the optional extensionality criterion. -/
def Extensionality : Prop :=
  PropositionalExtensionality (language false) ∧
  (∀ (W : Type), PropositionalExtensionality (allPredicates : Domain W)) ∧
  MC (pockets false).frame allPredicates .right ∧
  MC (pockets false).frame allPredicates .twin ∧
  Box (pockets false).frame (fun w => Dia (pockets false).frame
    (MC (pockets false).frame allPredicates) w) .root

/-- Rows reproduce the finite edge table, atoms and independent contingency. -/
def report (paired : Bool) : String :=
  reprStr ((pockets paired).worlds.map (fun w =>
    (w, (pockets paired).worlds.map (fun v => (v, (pockets paired).edge w v)),
      eval (pockets paired) w (.atom false), eval (pockets paired) w (.atom true),
      eval (pockets paired) w (.diamond (.atom false)),
      eval (pockets paired) w (.diamond (.neg (.atom false))))))
end TruthCore.Modal.S4Research
