module

public import TruthCore.Causality.CompleteCauseContributorCover
public import TruthCore.Causality.PluralRootConfluence
public import TruthCore.Causality.UnderivedCommonSource
public import TruthCore.Results.Causality.CompleteCauseContributorCover.Solution
public import TruthCore.Results.Causality.CompleteCauseSourceUniqueness.Solution
public import TruthCore.Results.Causality.PluralRootConfluence.Solution
public import TruthCore.Results.Causality.SourceForest.Solution
public import TruthCore.Results.Causality.UnderivedCommonSource.Solution

@[expose] public section

namespace TruthCore.Results.Causality.CompleteCauseUnderivedSource
open TruthCore.Causality
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Causality.NecessarilyUnderived
open TruthCore.Causality.WorldSourceRegress
open TruthCore.Causality.SourceForest
open TruthCore.Causality.CompleteCauseContributorCover
open TruthCore.Causality.UnderivedCommonSource
open TruthCore.Causality.NamedPotentialCauser

/-- Replace upstream confluence in the same-witness ordinary-causal result by
two complete-production contributor policies on the SAME actual causal graph.
The ambient order on actual nodes represents object parthood, not causation.
All five necessary-underived union premises, the causal-to-R map, and weak
connectivity remain explicit and OPEN. -/
theorem from_union {World Being : Type} (m : Ontic World Being)
    (R : World → Being → Being → Prop) (w : World)
    [PartialOrder (Actual m w)]
    (participants : Actual m w → Set (Actual m w))
    (hNecessary : NecessaryBeing m w)
    (hReflexive : ActualReflexive m w)
    (hNoContingent : NoContingentGroundOfNecessary m R w)
    (hUnionWF : WellFoundedUnionNecessarySupport m R w)
    (hEM : TruthCore.Logic.ExcludedMiddle)
    (hMap : ActualCauseSupportsEsse m R w)
    (hProducer : ProducerParticipates (actualGraph m w) participants)
    (hCover : CompleteCauseCoversContributors (actualGraph m w) participants)
    (hConnected : WeaklyConnected (actualGraph m w)) :
    CommonUnderivedActualSource m R w := by
  have hUniqueCause := TruthCore.Results.Causality.CompleteCauseContributorCover.uniqueCause
    (actualGraph m w) participants hProducer hCover
  have hPred : UniquePredecessor (actualGraph m w) := by
    intro a b e ha hb
    exact hUniqueCause e a b ha hb
  exact TruthCore.Results.Causality.UnderivedCommonSource.causal_from_union
    m R w hNecessary hReflexive hNoContingent hUnionWF hEM hMap hConnected
    (TruthCore.Results.Causality.SourceForest.confluent_of_uniquePredecessor
      (actualGraph m w) hPred)

/-- Weaken the scope of the two complete-cause policies: they concern only
the complete-production subgraph K, NOT every ordinary causal edge. K has
the same actual individual carrier, is included in ordinary causation, and
is itself weakly connected. Thus every ordinary source is a K-source. The
five #495 premises and the one-way causal-to-R interface yield the SAME
named necessarily underived witness as the unique ordinary source.
Whether complete production really spans all actual beings remains OPEN. -/
theorem from_subgraph_union {World Being : Type} (m : Ontic World Being)
    (R : World → Being → Being → Prop) (w : World)
    [PartialOrder (Actual m w)]
    (K : TruthCore.Logic.Regress.Graph (Actual m w))
    (participants : Actual m w → Set (Actual m w))
    (hNecessary : NecessaryBeing m w)
    (hReflexive : ActualReflexive m w)
    (hNoContingent : NoContingentGroundOfNecessary m R w)
    (hUnionWF : WellFoundedUnionNecessarySupport m R w)
    (hEM : TruthCore.Logic.ExcludedMiddle)
    (hMap : ActualCauseSupportsEsse m R w)
    (hIncluded : ∀ a b, K.edge a b → (actualGraph m w).edge a b)
    (hProducer : ProducerParticipates K participants)
    (hCover : CompleteCauseCoversContributors K participants)
    (hConnected : WeaklyConnected K) :
    CommonUnderivedActualSource m R w := by
  obtain ⟨n, hn, hNec, hNoSupport⟩ :=
    TruthCore.Results.Causality.NecessarilyUnderived.PositiveUnion.checks
      m R w hNecessary hReflexive hNoContingent hUnionWF hEM
  have hNamed : NamedNecessarilyUnderived m R w n :=
    ⟨hn, hNec, hNoSupport⟩
  have hSource : (actualGraph m w).Source ⟨n, hn⟩ := by
    apply (WorldSourceRegress.actualSource_iff m w _).mpr
    rintro ⟨source, hPresent, hCause⟩
    exact hNoSupport w source hPresent
      (hMap source n hPresent hn hCause)
  have hUnique : AtMostOneSource (actualGraph m w) :=
    TruthCore.Results.Causality.CompleteCauseSourceUniqueness.atMostOne_subgraph
      K (actualGraph m w) participants hIncluded hProducer hCover hConnected
  refine ⟨n, hNamed, hn, hSource, ?_⟩
  intro s hs
  exact congrArg Subtype.val (hUnique s ⟨n, hn⟩ hs hSource)

/-- The unchanged two-root model's two edges into the SAME effect cannot both
be complete-production edges under BOTH contributor policies for ANY ambient
parthood partial order and participant family. Plural partial cooperation is
not excluded: the policies only concern complete producers of this effect. -/
theorem plural_root_boundary
    [PartialOrder (Actual PartFreePlurality.ontic false)]
    (participants : Actual PartFreePlurality.ontic false →
      Set (Actual PartFreePlurality.ontic false)) :
    ¬ (ProducerParticipates PluralRootConfluence.graph participants ∧
      CompleteCauseCoversContributors PluralRootConfluence.graph participants) := by
  rintro ⟨hProducer, hCover⟩
  have hUniqueCause := TruthCore.Results.Causality.CompleteCauseContributorCover.uniqueCause
    PluralRootConfluence.graph participants hProducer hCover
  rcases TruthCore.Results.Causality.PluralRootConfluence.control with
    ⟨_, _, _, _, _, _, hDistinct, hLeftEdge, hRightEdge, _, _, _⟩
  exact hDistinct (hUniqueCause (PluralRootConfluence.node .instrument)
    (PluralRootConfluence.node .left) (PluralRootConfluence.node .right)
    hLeftEdge hRightEdge)

end TruthCore.Results.Causality.CompleteCauseUnderivedSource
