import TruthCore.Causality.HeadlessCausalAncestry
import TruthCore.Results.Causality.WorldSourceRegress.Solution

namespace TruthCore.Results.Causality.HeadlessCausalAncestry
open TruthCore.Causality.HeadlessCausalAncestry
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Logic.Regress

/-- Finite reachability is closed under every incoming edge, without choice. -/
theorem cone_closed {Node : Type} (G : Graph Node) (selected x y : Node)
    (hAnc : AncestorCone G selected x) (hEdge : G.edge y x) :
    AncestorCone G selected y :=
  Relation.ReflTransGen.head hEdge hAnc

/-- Positive availability gives headless full cones constructively. -/
theorem predecessors_iff_headless {Node : Type} (G : Graph Node) :
    (∀ x, ∃ y, G.edge y x) ↔ ∀ selected, HeadlessFullAncestry G selected := by
  constructor
  · intro hPred selected x hAnc
    obtain ⟨y, hEdge⟩ := hPred x
    exact ⟨y, cone_closed G selected x y hAnc hEdge, hEdge⟩
  · intro hHeadless x
    obtain ⟨y, _, hEdge⟩ := hHeadless x x Relation.ReflTransGen.refl
    exact ⟨y, hEdge⟩

/-- Only the negative-to-positive predecessor step uses explicit EM. -/
theorem no_sources_iff_headless {Node : Type} (G : Graph Node)
    (hEM : ExcludedMiddle) :
    (¬ ∃ s, G.Source s) ↔ ∀ selected, HeadlessFullAncestry G selected := by
  constructor
  · intro hNone
    apply (predecessors_iff_headless G).mp
    intro x
    rcases hEM (∃ y, G.edge y x) with hPred | hSource
    · exact hPred
    · exact (hNone ⟨x, hSource⟩).elim
  · intro hHeadless ⟨s, hSource⟩
    exact hSource ((predecessors_iff_headless G).mpr hHeadless s)

theorem checks (hEM : ExcludedMiddle) : HeadlessAncestryCharacterization := by
  intro Node G
  exact ⟨cone_closed G, predecessors_iff_headless G, no_sources_iff_headless G hEM⟩

/-- Failure of universal headless-cone coverage supplies some graph source.
Explicit EM is retained; the witness need not cause any further node. -/
theorem source_of_not_headless_coverage {Node : Type} (G : Graph Node)
    (hEM : ExcludedMiddle) (hNot : ¬ ∀ selected, HeadlessFullAncestry G selected) :
    ∃ s, G.Source s := by
  rcases hEM (∃ s, G.Source s) with hSource | hNone
  · exact hSource
  · exact (hNot (((checks hEM) Node G).2.2.mp hNone)).elim

/-- Apply the generic network result to the existing actual causal subtype.
The same `Ontic.Causes` at the same world occurs on both sides. No actuality
of absent sources, endpoint-soundness, concreteness or modal transport is assumed. -/
theorem actual_no_sources_iff_headless {W B : Type}
    (m : TruthCore.German.Kant.CosmologicalInference.Ontic W B) (w : W)
    (hEM : ExcludedMiddle) :
    (¬ ∃ x, m.ExistsAt w x ∧ ¬ ∃ y, m.ExistsAt w y ∧ m.Causes w y x) ↔
      ∀ selected : TruthCore.Causality.WorldSourceRegress.Actual m w,
        HeadlessFullAncestry (TruthCore.Causality.WorldSourceRegress.actualGraph m w) selected := by
  have hSources : (¬ ∃ x, m.ExistsAt w x ∧
      ¬ ∃ y, m.ExistsAt w y ∧ m.Causes w y x) ↔
      ¬ ∃ s, (TruthCore.Causality.WorldSourceRegress.actualGraph m w).Source s := by
    constructor
    · intro hNone ⟨s, hs⟩
      exact hNone ⟨s.val, s.property,
        (TruthCore.Results.Causality.WorldSourceRegress.actualSource_iff m w s).mp hs⟩
    · intro hNone ⟨x, hx, hNoCause⟩
      exact hNone ⟨⟨x, hx⟩,
        (TruthCore.Results.Causality.WorldSourceRegress.actualSource_iff m w ⟨x, hx⟩).mpr hNoCause⟩
  exact hSources.trans
    (no_sources_iff_headless (TruthCore.Causality.WorldSourceRegress.actualGraph m w) hEM)

end TruthCore.Results.Causality.HeadlessCausalAncestry
