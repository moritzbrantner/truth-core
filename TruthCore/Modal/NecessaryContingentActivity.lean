import TruthCore.German.Kant.CosmologicalInference

/-!
Issue #435: a small formal separation of necessary existence and contingent
causal activity. Reuse Kant's world-relative existence and causal relata; add
only the minimal soundness condition that a causal edge relates two distinct
entities existing at the world of that edge.

An outgoing causal edge is an *exercise* of causation, not a definition of an
unexercised power, substantial concreteness or metaphysical possibility.
-/
namespace TruthCore.Modal.NecessaryContingentActivity

open TruthCore.German.Kant.CosmologicalInference

variable {World Being : Type}

/-- Every causal arrow has a distinct, existing cause and effect. -/
def SoundDistinctCauses (m : Ontic World Being) : Prop :=
  ∀ w x y, m.Causes w x y →
    m.ExistsAt w x ∧ m.ExistsAt w y ∧ x ≠ y

/-- The given bearer actually causes something at this world. -/
def ExercisesCausation (m : Ontic World Being) (w : World) (x : Being) : Prop :=
  ∃ y, m.Causes w x y

/-- A universal-accessibility model with an existing necessary cause whose
exercise of causation varies between accessible worlds. -/
def NecessaryWithContingentActivity : Prop :=
  ∃ m : Ontic Bool Bool,
    (∀ w v, m.frame.access w v) ∧
    SoundDistinctCauses m ∧
    NecessaryBeing m false ∧
    ExercisesCausation m false false ∧
    ¬ ExercisesCausation m true false

/-- `false` exists in both worlds; `true` exists only in the first. The only
causal event is `false` causing `true` in that first world. -/
private def model : Ontic Bool Bool where
  frame := ⟨fun _ _ => True⟩
  ExistsAt := fun w x => x = false ∨ (w = false ∧ x = true)
  Causes := fun w x y => w = false ∧ x = false ∧ y = true

/-- Necessary existence and nontrivial but contingent causal activity are
jointly satisfiable under the displayed minimal causal constraints. -/
theorem necessaryWithContingentActivity : NecessaryWithContingentActivity := by
  refine ⟨model, ?_, ?_, ?_, ?_, ?_⟩
  · intro _ _
    trivial
  · intro w x y hCause
    change w = false ∧ x = false ∧ y = true at hCause
    rcases hCause with ⟨rfl, rfl, rfl⟩
    simp [model]
  · refine ⟨false, ?_, ?_⟩
    · simp [model]
    · intro v _
      simp [model]
  · refine ⟨true, ?_⟩
    simp [model]
  · intro ⟨y, hCause⟩
    simp [model] at hCause

end TruthCore.Modal.NecessaryContingentActivity
