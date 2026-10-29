import TruthCore.Causality.PartFreePlurality
import TruthCore.Causality.UnderivedCommonSource

/-! A graph view of the UNCHANGED #684 interpretation, not a second causal
semantics. Here and only here its chosen Causes and supportsEsse are both prior.
Actuality is the model's ExistsAt predicate, not evidence of real instantiation. -/
namespace TruthCore.Causality.PluralRootConfluence
open TruthCore.Causality
open TruthCore.Causality.PartFreePlurality
open TruthCore.Causality.SourceForest
open TruthCore.Causality.WorldSourceRegress

abbrev graph := actualGraph ontic false

def node (x : Being) : Actual ontic false := ⟨x, True.intro⟩

/-- The original joint certificate survives literally, together with a common
effect and two nonjoinable upstream source endpoints. The only failed input to
#634's rooted_from_source is confluence: connectivity and HasSource hold, even
WF holds. This is formal satisfiability, not real causal or metaphysical warrant. -/
def Control : Prop :=
  JointControl ∧
  graph = UnderivedCommonSource.actualSupportGraph ontic power.supportsEsse false ∧
  WeaklyConnected graph ∧ WellFoundedEdges graph ∧
  graph.Source (node .left) ∧ graph.Source (node .right) ∧
  node .left ≠ node .right ∧
  graph.edge (node .left) (node .instrument) ∧
  graph.edge (node .right) (node .instrument) ∧
  ¬ Relation.Join (Relation.ReflTransGen (fun x y => graph.edge y x))
    (node .left) (node .right) ∧
  ¬ UpstreamConfluent graph ∧ ¬ RootedAtUniqueSource graph

end TruthCore.Causality.PluralRootConfluence
