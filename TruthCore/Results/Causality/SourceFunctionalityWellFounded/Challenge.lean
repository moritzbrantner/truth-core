import TruthCore.Causality.AtomisticCausalSource
import TruthCore.Causality.SourceWitness

namespace TruthCore.Results.Causality.SourceFunctionalityWellFounded
open TruthCore.Logic.Regress (Graph)
open TruthCore.Causality.AtomisticCausalSource (SourceExists)
open TruthCore.Causality.SourceForest

/-- A supplied source, complete-graph connectivity and incoming functionality
force accessibility of every node. No WF premise is assumed; the graph's
causal interpretation, connectivity and source applicability remain open. -/
theorem wellFounded {B : Type} (G : Graph B)
    (hSource : SourceExists G) (hConnected : WeaklyConnected G)
    (hPred : UniquePredecessor G) : WellFoundedEdges G := by
  sorry

end TruthCore.Results.Causality.SourceFunctionalityWellFounded
