import TruthCore.Causality.AtomisticCausalSource
import TruthCore.Causality.SourceWitness
import TruthCore.Results.Causality.SourceWitness.Solution

namespace TruthCore.Results.Causality.SourceFunctionalityWellFounded
open TruthCore.Logic.Regress (Graph)
open TruthCore.Causality.AtomisticCausalSource (SourceExists)
open TruthCore.Causality.SourceForest

/-- A supplied source, weak connectivity of the same graph and incoming functionality
force accessibility of every node. No WF premise is assumed; the graph's
causal interpretation, connectivity and source applicability remain open. -/
theorem wellFounded {B : Type} (G : Graph B)
    (hSource : SourceExists G) (hConnected : WeaklyConnected G)
    (hPred : UniquePredecessor G) : WellFoundedEdges G := by
  have hConfluent :=
    TruthCore.Results.Causality.SourceForest.confluent_of_uniquePredecessor G hPred
  obtain ⟨s, hs, _hUnique, hPaths⟩ :=
    TruthCore.Results.Causality.SourceWitness.rooted_from_source G hConnected hConfluent hSource
  have accOfPath : ∀ x z, TruthCore.Causality.FiniteCausalPath G.edge x z →
      G.Source z → Acc G.edge x := by
    intro x z hPath
    induction hPath with
    | same z =>
      intro hSourceZ
      exact Acc.intro z (fun y hy => (hSourceZ ⟨y, hy⟩).elim)
    | @link x y z hEdge _hPath ih =>
      intro hSourceZ
      refine Acc.intro x ?_
      intro a hEdgeA
      have hSame : a = y := hPred hEdgeA hEdge
      subst a
      exact ih hSourceZ
  exact ⟨fun x => accOfPath x s (hPaths x) hs⟩

end TruthCore.Results.Causality.SourceFunctionalityWellFounded
