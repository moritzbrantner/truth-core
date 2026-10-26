module

public import Mathlib.Order.WellFoundedSet

/-!
# Finite distinct ancestry and causal loops (#367)

This is analyst vocabulary, not a sourced identification with Pruss's full modal
causal finitism. `cause y x` points upstream, from cause to effect. History is
Mathlib's nonempty finite transitive closure: it includes indirect ancestors,
not just immediate causes. Set finiteness counts distinct relata, not visits to
the same relatum. A one-node loop therefore has finite distinct ancestry.

All relations here share one carrier. This does not identify events with beings:
the inclusion premise must be defended for an interpretation on that carrier.
For event-based finitism a separate event/being translation is still required.
-/
@[expose] public section

namespace TruthCore.Case.Catholicism.StageOne.CausalFinitism

/-- Every relatum has finitely many distinct upstream ancestors, reached by one
or more causal edges. No uniform bound, time bound or modal quantifier is built in. -/
def FiniteDistinctAncestry {Entity : Type} (cause : Entity → Entity → Prop) : Prop :=
  ∀ x, Set.Finite {y | Relation.TransGen cause y x}

/-- No nonempty finite causal path returns to its start. This excludes cycles
of every finite length, not merely self-edges. -/
def NoCausalLoops {Entity : Type} (cause : Entity → Entity → Prop) : Prop :=
  ∀ x, ¬ Relation.TransGen cause x x

/-- Each per se efficient-cause edge is an edge of the relation whose ancestry
is finite. Same carrier and orientation are explicit; inclusion is not automatic. -/
def PerSeLinksIncluded {Being : Type}
    (cause perSe : Being → Being → Prop) : Prop :=
  ∀ ⦃y x⦄, perSe y x → cause y x

end TruthCore.Case.Catholicism.StageOne.CausalFinitism
