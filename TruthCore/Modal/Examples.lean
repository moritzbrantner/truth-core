import TruthCore.Modal.Cube

namespace TruthCore.Modal.Examples

open TruthCore.Modal

inductive World where
  | actual
  | nearby
  | remote
  deriving Repr, DecidableEq

inductive Atom where
  | p
  deriving Repr, DecidableEq

/-- A simple future-directed ordering of three worlds. -/
def rank : World → Nat
  | .actual => 0
  | .nearby => 1
  | .remote => 2

/-- A small S4 frame: a world can see itself and every world at least as far along. -/
def frame : Frame World where
  access world next := rank world ≤ rank next

/-- The frame is reflexive. -/
theorem frame_reflexive : Reflexive frame := by
  intro world
  exact Nat.le_refl (rank world)

/-- The frame is transitive. -/
theorem frame_transitive : Transitive frame := by
  intro world middle next hWorldMiddle hMiddleNext
  exact Nat.le_trans hWorldMiddle hMiddleNext

/-- Therefore this concrete graph is an S4 frame. -/
theorem frame_is_s4 : FrameSatisfies .S4 frame := by
  exact ⟨frame_reflexive, frame_transitive⟩

/-- It is intentionally not symmetric, so the example does not silently become S5. -/
theorem frame_not_symmetric : ¬ Symmetric frame := by
  intro hSymmetric
  have hBack := hSymmetric .actual .nearby (by decide)
  simp [frame, rank] at hBack

/-- Proposition p is true only at the remote world. -/
def valuation : Valuation World Atom := fun world _ => world = .remote

/-- From the actual world p is possible. -/
theorem actual_possible_p : Holds frame valuation .actual (.diamond (.atom .p)) := by
  exact ⟨.remote, by decide, rfl⟩

/-- From the actual world p is not yet necessary. -/
theorem actual_not_necessary_p : ¬ Holds frame valuation .actual (.box (.atom .p)) := by
  intro hNecessary
  have hActual := hNecessary .actual (by decide)
  simp [Holds, valuation] at hActual

/-- At the remote world, p is both true and necessary. -/
theorem remote_necessary_p : Holds frame valuation .remote (.box (.atom .p)) := by
  intro next hAccess
  cases next <;> simp [frame, rank] at hAccess ⊢

end TruthCore.Modal.Examples
