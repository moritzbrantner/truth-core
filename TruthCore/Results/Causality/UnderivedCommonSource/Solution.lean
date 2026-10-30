import TruthCore.Causality.UnderivedCommonSource
import TruthCore.Results.Causality.SourceForest.Solution
import TruthCore.Results.Causality.NecessarilyUnderived.PositiveUnion.Solution
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
  have hs : (actualSupportGraph m R w).Source ⟨n, hNamed.1⟩ := by
    rintro ⟨source, hEdge⟩
    exact hNamed.2.2 w source.val source.property hEdge
  refine ⟨hNamed.1, hs, ?_⟩
  intro source hSource
  have hSame := SourceForest.atMostOne_of_confluent
    (actualSupportGraph m R w) hConnected hConfluent
    source ⟨n, hNamed.1⟩ hSource hs
  exact congrArg Subtype.val hSame

/-- Preserve #495's same existential witness as the unique actual R-source.
This connects existing results without defending the structural premises. -/
theorem exists_support {World Being : Type} (m : Ontic World Being)
    (R : World → Being → Being → Prop) (w : World)
    (hUnderived : NecessarilyUnderived m R w)
    (hConnected : WeaklyConnected (actualSupportGraph m R w))
    (hConfluent : UpstreamConfluent (actualSupportGraph m R w)) :
    CommonUnderivedSupportSource m R w := by
  obtain ⟨n, hn, hNecessary, hNoSupport⟩ := hUnderived
  have hNamed : NamedNecessarilyUnderived m R w n := ⟨hn, hNecessary, hNoSupport⟩
  exact ⟨n, hNamed, named_support m R w n hNamed hConnected hConfluent⟩

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
  have hnSource : (actualGraph m w).Source ⟨n, hNamed.1⟩ := by
    apply (WorldSourceRegress.actualSource_iff m w _).mpr
    rintro ⟨source, hPresent, hCause⟩
    exact hNamed.2.2 w source hPresent
      (hMap source n hPresent hNamed.1 hCause)
  refine ⟨hNamed.1, hnSource, ?_⟩
  intro s hs
  have hSame := SourceForest.atMostOne_of_confluent
    (actualGraph m w) hConnected hConfluent s ⟨n, hNamed.1⟩ hs hnSource
  exact congrArg Subtype.val hSame

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
  obtain ⟨n, hn, hNecessary, hNoSupport⟩ := hUnderived
  have hNamed : NamedNecessarilyUnderived m R w n := ⟨hn, hNecessary, hNoSupport⟩
  exact ⟨n, hNamed, named m R w n hNamed hMap hConnected hConfluent⟩
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
  have hUnderived := TruthCore.Results.Causality.NecessarilyUnderived.PositiveUnion.checks
    m R w hNecessary hReflexive hNoContingent hUnionWF hEM
  exact exists_support m R w hUnderived hConnected hConfluent

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
  have hUnderived := TruthCore.Results.Causality.NecessarilyUnderived.PositiveUnion.checks
    m R w hNecessary hReflexive hNoContingent hUnionWF hEM
  exact exists_common m R w hUnderived hMap hConnected hConfluent

end TruthCore.Results.Causality.UnderivedCommonSource
