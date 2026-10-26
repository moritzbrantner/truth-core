import TruthCore.Causality.FiniteBranching

/-!
# Finite source inspections do not imply a global source

The relation is the already-checked successor-predecessor countermodel:
`cause y x` means `y = x + 1` on natural numbers. This is a source-free
mathematical counterexample, not a claim about physical regress.
-/
namespace TruthCore.Causality.FiniteRestriction

open TruthCore.Causality.FiniteBranching
open TruthCore.Case.Catholicism.StageOne.CausalFinitism

/-- Every finite nonempty induced subgraph contains a vertex without an
incoming causal edge *from within that subgraph*. -/
def EveryFiniteRestrictionHasLocalSource {Entity : Type}
    (cause : Entity → Entity → Prop) : Prop :=
  ∀ s : Finset Entity, s.Nonempty →
    ∃ x ∈ s, ¬ ∃ y ∈ s, cause y x

/-- The whole carrier has at least one vertex without any incoming causal
edge. The extension from local finite sources to this global one is invalid. -/
def HasGlobalSource {Entity : Type}
    (cause : Entity → Entity → Prop) : Prop :=
  ∃ x, ∀ y, ¬ cause y x

theorem reverseSuccessorHasFiniteLocalSources :
    EveryFiniteRestrictionHasLocalSource successorPredecessor := by
  intro s hs
  refine ⟨s.max' hs, Finset.max'_mem s hs, ?_⟩
  rintro ⟨y, hy, hEdge⟩
  have hBound : y ≤ s.max' hs := Finset.le_max' s y hy
  have hStrict : s.max' hs < y := by
    change y = s.max' hs + 1 at hEdge
    simpa [hEdge] using Nat.lt_succ_self (s.max' hs)
  exact (not_lt_of_ge hBound) hStrict

theorem reverseSuccessorNoGlobalSource :
    ¬ HasGlobalSource successorPredecessor := by
  rintro ⟨x, hx⟩
  exact hx (x + 1) rfl

private theorem reverseSuccessorPathStrict {y x : Nat}
    (h : Relation.TransGen successorPredecessor y x) : x < y := by
  induction h with
  | single hEdge =>
    change _ = _ + 1 at hEdge
    simp [hEdge]
  | tail hPath hEdge ih =>
    change _ = _ + 1 at hEdge
    exact Nat.lt_trans (by simp [hEdge]) ih

theorem reverseSuccessorNoLoops : NoCausalLoops successorPredecessor := by
  intro x hLoop
  exact (Nat.lt_irrefl x) (reverseSuccessorPathStrict hLoop)

/-- Compact finite-looking causal pieces coexist with an infinite, loop-free
graph that has no source. The finite-to-infinite quantifier shift is invalid. -/
theorem finiteLocalSourcesAndNoGlobalSource :
    EveryFiniteRestrictionHasLocalSource successorPredecessor ∧
    ¬ HasGlobalSource successorPredecessor ∧
    NoCausalLoops successorPredecessor := by
  exact ⟨reverseSuccessorHasFiniteLocalSources,
    reverseSuccessorNoGlobalSource, reverseSuccessorNoLoops⟩

/-- Constructively witnessed failure of the finite-subsystem-to-global-source
inference. The existential is over mathematical relations on `Nat`, not over
metaphysically possible physical causal histories. -/
def FiniteLocalWithoutGlobal : Prop :=
  ∃ cause : Nat → Nat → Prop,
    EveryFiniteRestrictionHasLocalSource cause ∧
    ¬ HasGlobalSource cause ∧
    NoCausalLoops cause

theorem finiteLocalWithoutGlobal : FiniteLocalWithoutGlobal := by
  exact ⟨successorPredecessor, finiteLocalSourcesAndNoGlobalSource⟩

end TruthCore.Causality.FiniteRestriction
