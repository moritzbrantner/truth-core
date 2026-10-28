import TruthCore.Causality.UnderivedCommonSource

namespace TruthCore.Results.Causality.UnderivedCommonSource
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Causality.NecessarilyUnderived
open TruthCore.Causality.NamedPotentialCauser
open TruthCore.Causality.WorldSourceRegress
open TruthCore.Causality.SourceForest
open TruthCore.Causality.UnderivedCommonSource

/-- Reuse confluence uniqueness on the SAME support relation R. Named actual
presence supplies population; no cause-to-support interface or WF is needed. -/
theorem named_support {World Being : Type} (m : Ontic World Being)
    (R : World → Being → Being → Prop) (w : World) (n : Being)
    (hNamed : NamedNecessarilyUnderived m R w n)
    (hConnected : WeaklyConnected (actualSupportGraph m R w))
    (hConfluent : UpstreamConfluent (actualSupportGraph m R w)) :
    UniqueActualSupportSourceAt m R w n := by
  sorry

/-- Preserve #495's same existential witness as the unique actual R-source.
This connects existing results without defending the structural premises. -/
theorem exists_support {World Being : Type} (m : Ontic World Being)
    (R : World → Being → Being → Prop) (w : World)
    (hUnderived : NecessarilyUnderived m R w)
    (hConnected : WeaklyConnected (actualSupportGraph m R w))
    (hConfluent : UpstreamConfluent (actualSupportGraph m R w)) :
    CommonUnderivedSupportSource m R w := by
  sorry

/-- Map the same named witness to the actual-node graph, then reuse checked
source uniqueness. Connectedness, upstream confluence and the causal-to-support
interface are open premises. No ordinary-world WF, reciprocal potential
causation or maximality is used. -/
theorem named {World Being : Type} (m : Ontic World Being)
    (R : World → Being → Being → Prop) (w : World) (n : Being)
    (hNamed : NamedNecessarilyUnderived m R w n)
    (hMap : ActualCauseSupportsEsse m R w)
    (hConnected : WeaklyConnected (actualGraph m w))
    (hConfluent : UpstreamConfluent (actualGraph m w)) :
    UniqueActualSourceAt m w n := by
  sorry

/-- Unpack exactly #495's existential conclusion; retain the same individual
for source uniqueness. Named presence supplies population. Necessity is retained
for that witness, not inferred from graph structure. -/
theorem exists_common {World Being : Type} (m : Ontic World Being)
    (R : World → Being → Being → Prop) (w : World)
    (hUnderived : NecessarilyUnderived m R w)
    (hMap : ActualCauseSupportsEsse m R w)
    (hConnected : WeaklyConnected (actualGraph m w))
    (hConfluent : UpstreamConfluent (actualGraph m w)) :
    CommonUnderivedActualSource m R w := by
  sorry
/-- End-to-end composition imports the existing #495 result with all FIVE
original premises. Union WF on necessary R-support is RETAINED; no ordinary
world-causal WF is introduced. Then preserve its witness through the graph lift. -/
theorem from_union {World Being : Type} (m : Ontic World Being)
    (R : World → Being → Being → Prop) (w : World)
    (hNecessary : NecessaryBeing m w)
    (hReflexive : ActualReflexive m w)
    (hNoContingent : NoContingentGroundOfNecessary m R w)
    (hUnionWF : WellFoundedUnionNecessarySupport m R w)
    (hEM : TruthCore.Logic.ExcludedMiddle)
    (hConnected : WeaklyConnected (actualSupportGraph m R w))
    (hConfluent : UpstreamConfluent (actualSupportGraph m R w)) :
    CommonUnderivedSupportSource m R w := by
  sorry

/-- Ordinary causal alternative retains the SAME five #495 premises, adds the
explicit open actual-cause/support map, and puts structural graph premises on
actualGraph m w. No causal-grounding identity is assumed by definition. -/
theorem causal_from_union {World Being : Type} (m : Ontic World Being)
    (R : World → Being → Being → Prop) (w : World)
    (hNecessary : NecessaryBeing m w)
    (hReflexive : ActualReflexive m w)
    (hNoContingent : NoContingentGroundOfNecessary m R w)
    (hUnionWF : WellFoundedUnionNecessarySupport m R w)
    (hEM : TruthCore.Logic.ExcludedMiddle)
    (hMap : ActualCauseSupportsEsse m R w)
    (hConnected : WeaklyConnected (actualGraph m w))
    (hConfluent : UpstreamConfluent (actualGraph m w)) :
    CommonUnderivedActualSource m R w := by
  sorry

end TruthCore.Results.Causality.UnderivedCommonSource
