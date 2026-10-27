import TruthCore.Case.Catholicism.StageOne.CausalFinitism
import TruthCore.Results.Case.Catholicism.CausalFinitism.Solution
import TruthCore.Logic.Regress

/-!
# Finite immediate causes, infinite ancestry, and well-foundedness

Source-free mathematical investigation of CAU-07/08 and #367/#441. The
relation `cause y x` points from a direct upstream cause to its dependent.
Well-foundedness is the inductive `Acc` condition on this *same* relation,
not a claim that every observed causal relation is well-founded, nor a bound
on temporal duration or on the number of possible-world alternatives.
-/
namespace TruthCore.Causality.FiniteBranching

open TruthCore.Case.Catholicism.StageOne.CausalFinitism

/-- Every node has a finite *set* of direct upstream causes. This permits
infinitely many nodes in the graph and arbitrarily large finite in-degrees. -/
def FiniteImmediatePredecessors {Entity : Type}
    (cause : Entity → Entity → Prop) : Prop :=
  ∀ x, Set.Finite {y | cause y x}

/-- Every node is accessible from its direct predecessors. This excludes
infinite descending causal sequences and finite causal cycles, but does not
impose finite fan-in or a temporal beginning. -/
def WellFoundedPredecessors {Entity : Type}
    (cause : Entity → Entity → Prop) : Prop :=
  WellFounded cause

/-- Well-foundedness plus locally finite predecessor sets forces each node's
entire transitive ancestral cone to be finite. This is the finitely-branching
finite-to-infinite bridge, with no uniform bound on ancestry size. -/
theorem finiteAncestry_of_wellFounded_finiteImmediate {Entity : Type}
    (cause : Entity → Entity → Prop)
    (hWF : WellFounded cause)
    (hFinite : FiniteImmediatePredecessors cause) :
    FiniteDistinctAncestry cause := by
  intro x
  induction hWF.apply x with
  | intro x _ ih =>
    have hUnion :
        (⋃ z ∈ {z | cause z x}, insert z {y | Relation.TransGen cause y z}).Finite :=
      (hFinite x).biUnion (fun z hz => (ih z hz).insert z)
    apply hUnion.subset
    intro y hy
    cases hy with
    | single hEdge =>
      exact Set.mem_iUnion.mpr ⟨y,
        Set.mem_iUnion.mpr ⟨hEdge, Set.mem_insert y _⟩⟩
    | tail hPath hEdge =>
      exact Set.mem_iUnion.mpr ⟨_,
        Set.mem_iUnion.mpr ⟨hEdge, Set.mem_insert_of_mem _ hPath⟩⟩

/-- Under finite immediate branching, well-foundedness is equivalent to
finite distinct ancestry *and* exclusion of finite cycles. The reverse
direction reuses the earlier #367 proof rather than rebuilding it. -/
theorem wellFounded_iff_finiteAncestry_and_noLoops {Entity : Type}
    (cause : Entity → Entity → Prop)
    (hFinite : FiniteImmediatePredecessors cause) :
    WellFounded cause ↔ FiniteDistinctAncestry cause ∧ NoCausalLoops cause := by
  constructor
  · intro hWF
    exact ⟨finiteAncestry_of_wellFounded_finiteImmediate cause hWF hFinite,
      (TruthCore.Logic.Regress.Graph.controls_of_wellFounded ⟨cause⟩ hWF).1⟩
  · rintro ⟨hAncestry, hLoops⟩
    exact ⟨TruthCore.Results.Case.Catholicism.CausalFinitism.perSeNoRegressOfFiniteAncestry
      cause cause hAncestry hLoops (by intro y x h; exact h)⟩

/-- A two-level, infinitely branching directed star: every `some n` is a
direct predecessor of `none`, and no `some n` has a predecessor. -/
def infinitelyWideStar (y x : Option Nat) : Prop :=
  x = none ∧ ∃ n, y = some n

theorem infinitelyWideStarWellFounded : WellFounded infinitelyWideStar := by
  refine ⟨fun x => ?_⟩
  cases x with
  | none =>
    apply Acc.intro
    intro y hy
    rcases hy with ⟨_, n, rfl⟩
    apply Acc.intro
    intro z hz
    cases hz.1
  | some n =>
    apply Acc.intro
    intro y hy
    cases hy.1

theorem infinitelyWideStarNotFiniteAncestry :
    ¬ FiniteDistinctAncestry infinitelyWideStar := by
  intro hFinite
  have hRange : (Set.range (fun n : Nat => some n)).Finite :=
    (hFinite none).subset (by
      intro y hy
      rcases hy with ⟨n, rfl⟩
      exact Relation.TransGen.single ⟨rfl, n, rfl⟩)
  exact Set.infinite_range_of_injective
    (fun a b h => Option.some.inj h) hRange

/-- A Nat successor chain has one direct predecessor at each node, but
is not well-founded in the cause-to-dependent orientation. -/
def successorPredecessor (y x : Nat) : Prop := y = x + 1

theorem successorPredecessorFiniteImmediate :
    FiniteImmediatePredecessors successorPredecessor := by
  intro x
  change Set.Finite {y | y = x + 1}
  exact Set.finite_singleton (x + 1)

theorem successorPredecessorNotWellFounded :
    ¬ WellFounded successorPredecessor := by
  intro hWF
  have bad : ∀ x, Acc successorPredecessor x → False := by
    intro x hx
    induction hx with
    | intro x _ ih => exact ih (x + 1) rfl
  exact bad 0 (hWF.apply 0)

/-- Both hypotheses really matter: well-foundedness alone permits infinite
ancestry through infinite local branching; finite local branching alone
permits a never-ending backward chain. -/
theorem independentOmissions :
    (∃ cause : Option Nat → Option Nat → Prop,
      WellFounded cause ∧ ¬ FiniteDistinctAncestry cause) ∧
    (∃ cause : Nat → Nat → Prop,
      FiniteImmediatePredecessors cause ∧ ¬ WellFounded cause) := by
  exact ⟨⟨infinitelyWideStar, infinitelyWideStarWellFounded,
    infinitelyWideStarNotFiniteAncestry⟩,
    ⟨successorPredecessor, successorPredecessorFiniteImmediate,
      successorPredecessorNotWellFounded⟩⟩

end TruthCore.Causality.FiniteBranching
