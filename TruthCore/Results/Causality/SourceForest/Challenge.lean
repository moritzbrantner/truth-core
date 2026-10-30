import TruthCore.Causality.SourceForest
namespace TruthCore.Results.Causality.SourceForest
open TruthCore.Logic.Regress
open TruthCore.Causality.SourceForest

theorem atMostOne {Node : Type} (G : Graph Node)
    (hConnected : WeaklyConnected G) (hPred : UniquePredecessor G) :
    AtMostOneSource G := by sorry

theorem rooted {Node : Type} (G : Graph Node)
    (hConnected : WeaklyConnected G) (hPred : UniquePredecessor G)
    (hWF : WellFoundedEdges G) (hPop : Populated G) :
    RootedAtUniqueSource G := by sorry

theorem controls : OmissionControls := by sorry
end TruthCore.Results.Causality.SourceForest
