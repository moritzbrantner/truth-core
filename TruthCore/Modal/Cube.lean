import TruthCore.Modal.Kripke

universe u v

namespace TruthCore.Modal

variable {World : Type u} {Atom : Type v}

/-- The fifteen non-redundant normal modal logics in the classical modal cube. -/
inductive System where
  | K
  | KB
  | K4
  | K5
  | K45
  | KD
  | KDB
  | KD4
  | KD5
  | KD45
  | KT
  | KTB
  | S4
  | KB5
  | S5
  deriving Repr, DecidableEq

/-- Semantic frame requirements for each modal-cube node.

The definitions intentionally use the smallest convenient frame-condition basis for
special nodes such as S5. The closure theorems below recover the familiar implied
conditions rather than duplicating them in the definition.
-/
def FrameSatisfies (system : System) (frame : Frame World) : Prop :=
  match system with
  | .K => True
  | .KB => Symmetric frame
  | .K4 => Transitive frame
  | .K5 => Euclidean frame
  | .K45 => Transitive frame ∧ Euclidean frame
  | .KD => Serial frame
  | .KDB => Serial frame ∧ Symmetric frame
  | .KD4 => Serial frame ∧ Transitive frame
  | .KD5 => Serial frame ∧ Euclidean frame
  | .KD45 => Serial frame ∧ Transitive frame ∧ Euclidean frame
  | .KT => Reflexive frame
  | .KTB => Reflexive frame ∧ Symmetric frame
  | .S4 => Reflexive frame ∧ Transitive frame
  | .KB5 => Symmetric frame ∧ Euclidean frame
  | .S5 => Reflexive frame ∧ Euclidean frame

/-- T frames are necessarily D frames because reflexivity provides a successor. -/
theorem kt_implies_kd (frame : Frame World) :
    FrameSatisfies .KT frame → FrameSatisfies .KD frame := by
  intro hKT
  exact reflexive_implies_serial frame hKT

/-- B+5 semantically entails 4, which is why KB5 and KB45 collapse. -/
theorem kb5_implies_k45 (frame : Frame World) :
    FrameSatisfies .KB5 frame → FrameSatisfies .K45 frame := by
  intro hKB5
  exact ⟨symmetric_euclidean_implies_transitive frame hKB5.1 hKB5.2, hKB5.2⟩

/-- S5 entails S4 at the frame level. -/
theorem s5_implies_s4 (frame : Frame World) :
    FrameSatisfies .S5 frame → FrameSatisfies .S4 frame := by
  intro hS5
  exact ⟨hS5.1, reflexive_euclidean_implies_transitive frame hS5.1 hS5.2⟩

/-- S5 entails KTB at the frame level. -/
theorem s5_implies_ktb (frame : Frame World) :
    FrameSatisfies .S5 frame → FrameSatisfies .KTB frame := by
  intro hS5
  exact ⟨hS5.1, reflexive_euclidean_implies_symmetric frame hS5.1 hS5.2⟩

/-- S5 entails KB5 at the frame level. -/
theorem s5_implies_kb5 (frame : Frame World) :
    FrameSatisfies .S5 frame → FrameSatisfies .KB5 frame := by
  intro hS5
  exact ⟨reflexive_euclidean_implies_symmetric frame hS5.1 hS5.2, hS5.2⟩

/-- S5 entails KD45 at the frame level. -/
theorem s5_implies_kd45 (frame : Frame World) :
    FrameSatisfies .S5 frame → FrameSatisfies .KD45 frame := by
  intro hS5
  exact ⟨
    reflexive_implies_serial frame hS5.1,
    reflexive_euclidean_implies_transitive frame hS5.1 hS5.2,
    hS5.2
  ⟩

/-- An S5 frame validates all five familiar optional modal-cube schemes. -/
theorem s5_validates_modal_cube_axioms
    (frame : Frame World)
    (hS5 : FrameSatisfies .S5 frame)
    (φ : Formula Atom) :
    Valid frame (.imp (.box φ) (.diamond φ)) ∧
      Valid frame (.imp (.box φ) φ) ∧
      Valid frame (.imp φ (.box (.diamond φ))) ∧
      Valid frame (.imp (.box φ) (.box (.box φ))) ∧
      Valid frame (.imp (.diamond φ) (.box (.diamond φ))) := by
  have hSerial := reflexive_implies_serial frame hS5.1
  have hSymmetric := reflexive_euclidean_implies_symmetric frame hS5.1 hS5.2
  have hTransitive := reflexive_euclidean_implies_transitive frame hS5.1 hS5.2
  exact ⟨
    axiomD_valid frame hSerial φ,
    axiomT_valid frame hS5.1 φ,
    axiomB_valid frame hSymmetric φ,
    axiom4_valid frame hTransitive φ,
    axiom5_valid frame hS5.2 φ
  ⟩

end TruthCore.Modal
