universe u v

namespace TruthCore.Modal

/-- A small propositional modal language for the modal-logic MVP. -/
inductive Formula (Atom : Type v) where
  | atom : Atom → Formula Atom
  | falsum : Formula Atom
  | imp : Formula Atom → Formula Atom → Formula Atom
  | box : Formula Atom → Formula Atom
  | diamond : Formula Atom → Formula Atom
  deriving Repr, DecidableEq

namespace Formula

variable {Atom : Type v}

/-- Classical negation encoded with implication and falsity. -/
def neg (φ : Formula Atom) : Formula Atom := .imp φ .falsum

/-- Conjunction, used only as a convenient derived connective in examples. -/
def conj (φ ψ : Formula Atom) : Formula Atom := neg (.imp φ (neg ψ))

end Formula

/-- A Kripke frame consists only of worlds and an accessibility relation. -/
structure Frame (World : Type u) where
  access : World → World → Prop

/-- Atomic truth assignments are intentionally separate from the frame. -/
abbrev Valuation (World : Type u) (Atom : Type v) := World → Atom → Prop

variable {World : Type u} {Atom : Type v}

/-- Truth of a modal formula at one world in one Kripke model. -/
def Holds (frame : Frame World) (valuation : Valuation World Atom) (world : World) : Formula Atom → Prop
  | .atom atom => valuation world atom
  | .falsum => False
  | .imp φ ψ => Holds frame valuation world φ → Holds frame valuation world ψ
  | .box φ => ∀ next, frame.access world next → Holds frame valuation next φ
  | .diamond φ => ∃ next, frame.access world next ∧ Holds frame valuation next φ

/-- Frame validity quantifies over every valuation and every world. -/
def Valid (frame : Frame World) (formula : Formula Atom) : Prop :=
  ∀ valuation world, Holds frame valuation world formula

/-- Every world accesses at least one world. -/
def Serial (frame : Frame World) : Prop :=
  ∀ world, ∃ next, frame.access world next

/-- Every world accesses itself. -/
def Reflexive (frame : Frame World) : Prop :=
  ∀ world, frame.access world world

/-- Accessibility can be traversed in either direction. -/
def Symmetric (frame : Frame World) : Prop :=
  ∀ world next, frame.access world next → frame.access next world

/-- Two accessibility steps can be collapsed to one. -/
def Transitive (frame : Frame World) : Prop :=
  ∀ world middle next,
    frame.access world middle → frame.access middle next → frame.access world next

/-- Worlds accessible from a common origin access one another. -/
def Euclidean (frame : Frame World) : Prop :=
  ∀ world left right,
    frame.access world left → frame.access world right → frame.access left right

/-- K is valid on every Kripke frame. -/
theorem axiomK_valid (frame : Frame World) (φ ψ : Formula Atom) :
    Valid frame (.imp (.box (.imp φ ψ)) (.imp (.box φ) (.box ψ))) := by
  intro valuation world hImp hPhi next hAccess
  exact hImp next hAccess (hPhi next hAccess)

/-- T (called M in the SEP modal-logic map) is valid on reflexive frames. -/
theorem axiomT_valid (frame : Frame World) (hReflexive : Reflexive frame) (φ : Formula Atom) :
    Valid frame (.imp (.box φ) φ) := by
  intro valuation world hBox
  exact hBox world (hReflexive world)

/-- D is valid on serial frames. -/
theorem axiomD_valid (frame : Frame World) (hSerial : Serial frame) (φ : Formula Atom) :
    Valid frame (.imp (.box φ) (.diamond φ)) := by
  intro valuation world hBox
  obtain ⟨next, hAccess⟩ := hSerial world
  exact ⟨next, hAccess, hBox next hAccess⟩

/-- B is valid on symmetric frames. -/
theorem axiomB_valid (frame : Frame World) (hSymmetric : Symmetric frame) (φ : Formula Atom) :
    Valid frame (.imp φ (.box (.diamond φ))) := by
  intro valuation world hPhi next hAccess
  exact ⟨world, hSymmetric world next hAccess, hPhi⟩

/-- 4 is valid on transitive frames. -/
theorem axiom4_valid (frame : Frame World) (hTransitive : Transitive frame) (φ : Formula Atom) :
    Valid frame (.imp (.box φ) (.box (.box φ))) := by
  intro valuation world hBox middle hWorldMiddle next hMiddleNext
  exact hBox next (hTransitive world middle next hWorldMiddle hMiddleNext)

/-- 5 is valid on Euclidean frames. -/
theorem axiom5_valid (frame : Frame World) (hEuclidean : Euclidean frame) (φ : Formula Atom) :
    Valid frame (.imp (.diamond φ) (.box (.diamond φ))) := by
  intro valuation world hPossible left hWorldLeft
  obtain ⟨right, hWorldRight, hPhi⟩ := hPossible
  exact ⟨right, hEuclidean world left right hWorldLeft hWorldRight, hPhi⟩

/-- Reflexivity already guarantees seriality, explaining the familiar T ⇒ D collapse. -/
theorem reflexive_implies_serial (frame : Frame World) (hReflexive : Reflexive frame) :
    Serial frame := by
  intro world
  exact ⟨world, hReflexive world⟩

/-- Reflexivity plus Euclideanness forces symmetry. -/
theorem reflexive_euclidean_implies_symmetric
    (frame : Frame World)
    (hReflexive : Reflexive frame)
    (hEuclidean : Euclidean frame) :
    Symmetric frame := by
  intro world next hAccess
  exact hEuclidean world next world hAccess (hReflexive world)

/-- Reflexivity plus Euclideanness also forces transitivity. -/
theorem reflexive_euclidean_implies_transitive
    (frame : Frame World)
    (hReflexive : Reflexive frame)
    (hEuclidean : Euclidean frame) :
    Transitive frame := by
  have hSymmetric := reflexive_euclidean_implies_symmetric frame hReflexive hEuclidean
  intro world middle next hWorldMiddle hMiddleNext
  exact hEuclidean middle world next (hSymmetric world middle hWorldMiddle) hMiddleNext

/-- Symmetry plus transitivity forces Euclideanness. -/
theorem symmetric_transitive_implies_euclidean
    (frame : Frame World)
    (hSymmetric : Symmetric frame)
    (hTransitive : Transitive frame) :
    Euclidean frame := by
  intro world left right hWorldLeft hWorldRight
  exact hTransitive left world right (hSymmetric world left hWorldLeft) hWorldRight

/-- Symmetry plus Euclideanness forces transitivity. -/
theorem symmetric_euclidean_implies_transitive
    (frame : Frame World)
    (hSymmetric : Symmetric frame)
    (hEuclidean : Euclidean frame) :
    Transitive frame := by
  intro world middle next hWorldMiddle hMiddleNext
  exact hEuclidean middle world next (hSymmetric world middle hWorldMiddle) hMiddleNext

end TruthCore.Modal
