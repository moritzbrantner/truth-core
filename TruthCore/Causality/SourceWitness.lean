import TruthCore.Causality.SourceForest

/-! Analyst structural follow-up: upstream confluence controls finite paths
once a graph-relative source EXISTS, without assuming well-foundedness. -/
namespace TruthCore.Causality.SourceWitness
open TruthCore.Logic.Regress
open TruthCore.Causality.SourceForest
open TruthCore.Causality.WorldSourceRegress

def HasSource {Node : Type} (G : Graph Node) : Prop := ∃ s, G.Source s

/-- The unchanged literal overlap graph has confluent upstream paths and one
source reached finitely from every node, while the SAME selected actual node
admits an injective infinite upstream chain and is inaccessible. -/
def ConfluentOverlapControl : Prop :=
  let G := actualGraph overlap ()
  WeaklyConnected G ∧ UpstreamConfluent G ∧ RootedAtUniqueSource G ∧
    ActualAcyclic overlap ∧ AnchoredRegress G overlapNode ∧
    ¬ Acc G.edge overlapNode ∧ ¬ WellFoundedEdges G
end TruthCore.Causality.SourceWitness
