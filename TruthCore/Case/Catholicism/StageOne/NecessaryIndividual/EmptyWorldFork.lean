import TruthCore.Case.Catholicism.StageOne.NecessaryIndividual.Quantifiers

/-!
Unattributed mathematical controls for the shared-root / empty-extension fork.
The accessibility relation is supplied, not identified with temporal succession.
Presence is distinct from causal explanation, and an empty presence extension
at a world is not the empty Lean type of worlds. Neither finite interpretation
is asserted to describe a metaphysically possible or actual universe.
-/
namespace TruthCore.Case.Catholicism.StageOne.NecessaryIndividual

open TruthCore.Modal
open TruthCore.Isabelle.AFP.NotesOnGoedel.GoedelVariantHOML1 (ExistsAt)

universe u v
variable {W : Type u} {I : Type v}

/-- A *fixed* roster member is present at every populated successor of `w`.
This records co-presence only, not a grounding or causal claim. -/
def SharedRootOnPopulated (F : Frame W) (present : ExistsAt W I)
    (w : W) (root : I) : Prop :=
  ∀ next, F.access w next → (∃ x, present x next) → present root next

/-- The root-presence hypothesis yields de-re necessity exactly when every
accessible world is populated. The witness must be shared across worlds. -/
def SharedRootBridgeLaw : Prop :=
  ∀ (World Individual : Type) (F : Frame World)
    (present : ExistsAt World Individual) (w : World),
    DeRe F present w ↔
      (DeDicto F present w ∧ ∃ root, SharedRootOnPopulated F present w root)

/-- Three accessible world labels: zero has an empty presence extension;
one and two have a shared root (individual zero) and distinct dependents. -/
def rootedEmptyFrame : Frame (Fin 3) := ⟨fun _ _ => True⟩

/-- Closed ordinal constructors with direct arithmetic bounds; using the
computed `Fin` numeral instances in proposition statements can draw in
unwanted proof axioms from their implementation. -/
def rootedZero : Fin 3 := ⟨0, Nat.zero_lt_succ 2⟩
def rootedOne : Fin 3 := ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ 1)⟩
def rootedTwo : Fin 3 :=
  ⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ 0))⟩

def rootedEmptyExists : ExistsAt (Fin 3) (Fin 3) :=
  fun individual world => world ≠ rootedZero ∧ (individual = rootedZero ∨ individual = world)

/-- Kernel-reducible numeral distinctions, without appealing to a global
propositional decidability instance or extending the permitted axiom set. -/
theorem firstHistory_ne_empty : rootedOne ≠ rootedZero := by
  intro h
  have hval : (1 : Nat) = 0 := congrArg Fin.val h
  exact Nat.noConfusion hval

theorem secondHistory_ne_empty : rootedTwo ≠ rootedZero := by
  intro h
  have hval : (2 : Nat) = 0 := congrArg Fin.val h
  exact Nat.noConfusion hval


/-- Only a present shared root can cause a present, distinct dependent.
This deliberately does not define a cause of the root itself. -/
def rootedEmptyCauses (world cause effect : Fin 3) : Prop :=
  rootedEmptyExists cause world ∧ rootedEmptyExists effect world ∧
    cause = rootedZero ∧ effect ≠ rootedZero

/-- Every present nonroot has a cause at its world. This is not unrestricted
PSR, since it does not require an explanation of the root. -/
def RootedEmptyDependentCoverage : Prop :=
  ∀ world effect, rootedEmptyExists effect world → effect ≠ rootedZero →
    ∃ cause, rootedEmptyCauses world cause effect

/-- Causal ancestry in this model has depth at most one edge; the modal
counterexample therefore does not depend on an infinite causal regress. -/
def RootedEmptyNoTwoStepCause : Prop :=
  ∀ world a b c, rootedEmptyCauses world a b → ¬ rootedEmptyCauses world b c

/-- A root present in every populated history, actual population, complete
causal coverage for dependents and a one-edge causal bound coexist with an
accessible empty extension and the failure of de-re necessity. -/
def RootedEmptyCountermodel : Prop :=
  Reflexive rootedEmptyFrame ∧
  rootedEmptyFrame.access rootedOne rootedZero ∧
  (∃ x, rootedEmptyExists x rootedOne) ∧
  SharedRootOnPopulated rootedEmptyFrame rootedEmptyExists rootedOne rootedZero ∧
  JointAbsence rootedEmptyFrame rootedEmptyExists rootedOne ∧
  ¬ DeDicto rootedEmptyFrame rootedEmptyExists rootedOne ∧
  ¬ DeRe rootedEmptyFrame rootedEmptyExists rootedOne ∧
  RootedEmptyDependentCoverage ∧
  RootedEmptyNoTwoStepCause

/-- Restrict attention to the two populated histories without changing their
existence extensions. Universal accessibility remains the same in kind. -/
def historyOnlyExists : ExistsAt Bool (Fin 3) :=
  fun individual history =>
    rootedEmptyExists individual (if history then rootedTwo else rootedOne)

/-- On this smaller world carrier the *same* root becomes necessarily present.
This is sensitivity to the admissible-world domain, not a metaphysical proof
that the empty history is inadmissible. -/
def HistoryOnlyCountermodel : Prop :=
  Reflexive alternatingFrame ∧
  (∀ x, historyOnlyExists x false ↔ rootedEmptyExists x rootedOne) ∧
  (∀ x, historyOnlyExists x true ↔ rootedEmptyExists x rootedTwo) ∧
  SharedRootOnPopulated alternatingFrame historyOnlyExists false rootedZero ∧
  DeDicto alternatingFrame historyOnlyExists false ∧
  DeRe alternatingFrame historyOnlyExists false ∧
  ¬ JointAbsence alternatingFrame historyOnlyExists false

end TruthCore.Case.Catholicism.StageOne.NecessaryIndividual
