import TruthCore.Causality.SourceWitness
namespace TruthCore.Results.Causality.SourceWitness
open TruthCore.Logic.Regress
open TruthCore.Causality.SourceForest
open TruthCore.Causality.SourceWitness

theorem rooted_from_source {Node : Type} (G : Graph Node)
    (hConnected : WeaklyConnected G) (hConfluent : UpstreamConfluent G)
    (hSource : HasSource G) : RootedAtUniqueSource G := by sorry

theorem overlap_control : ConfluentOverlapControl := by sorry
end TruthCore.Results.Causality.SourceWitness
