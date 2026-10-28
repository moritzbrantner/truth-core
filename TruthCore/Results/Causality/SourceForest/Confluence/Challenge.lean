import TruthCore.Causality.SourceForest
namespace TruthCore.Results.Causality.SourceForest
open TruthCore.Logic.Regress
open TruthCore.Causality.SourceForest

theorem confluent_of_uniquePredecessor {Node : Type} (G : Graph Node)
    (hPred : UniquePredecessor G) : UpstreamConfluent G := by sorry

theorem atMostOne_of_confluent {Node : Type} (G : Graph Node)
    (hConnected : WeaklyConnected G) (hConfluent : UpstreamConfluent G) :
    AtMostOneSource G := by sorry

theorem rooted_of_confluent {Node : Type} (G : Graph Node)
    (hConnected : WeaklyConnected G) (hConfluent : UpstreamConfluent G)
    (hWF : WellFoundedEdges G) (hPop : Populated G) :
    RootedAtUniqueSource G := by sorry

theorem confluence_strictness : ConfluenceStrictnessControl := by sorry
end TruthCore.Results.Causality.SourceForest
