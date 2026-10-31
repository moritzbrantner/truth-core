import TruthCore.Causality.WorldSourceRegress
import TruthCore.Logic.ExcludedMiddle

/-! Source-agnostic branching-network reconstruction of the survey A2
mathematical question. Edges retain the supplied Graph meaning. A full ancestor
cone is not assumed linear, acyclic, well-founded, infinite, concrete or actual.
Actual application uses the existing WorldSourceRegress actual-node subtype.
Nothing identifies ordinary causation with existential grounding. -/
namespace TruthCore.Causality.HeadlessCausalAncestry
open TruthCore.Logic.Regress

/-- All finite predecessors of `selected`, including `selected` itself.
This specializes Mathlib reflexive-transitive closure, not a chosen sequence. -/
def AncestorCone {Node : Type} (G : Graph Node) (selected : Node) : Set Node :=
  fun x => Relation.ReflTransGen G.edge x selected

/-- Every node of the FULL cone has some predecessor in that same cone.
Cycles and self-loops count; no infinitude or distinct-node chain is asserted. -/
def HeadlessFullAncestry {Node : Type} (G : Graph Node) (selected : Node) : Prop :=
  ∀ x, AncestorCone G selected x → ∃ y, AncestorCone G selected y ∧ G.edge y x

/-- Universal closure, positive predecessor-availability equivalence, and the
classical no-source characterization. Empty carriers satisfy these universals
vacuously. A cone need not exclude other cones or have a unique predecessor. -/
def HeadlessAncestryCharacterization : Prop :=
  ∀ (Node : Type) (G : Graph Node),
    (∀ selected x y, AncestorCone G selected x → G.edge y x →
      AncestorCone G selected y) ∧
    ((∀ x, ∃ y, G.edge y x) ↔ ∀ selected, HeadlessFullAncestry G selected) ∧
    ((¬ ∃ s, G.Source s) ↔ ∀ selected, HeadlessFullAncestry G selected)

end TruthCore.Causality.HeadlessCausalAncestry
