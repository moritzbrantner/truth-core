import TruthCore.Causality.CompleteCauseContributorCover
import TruthCore.Causality.PluralRootConfluence
import TruthCore.Causality.UnderivedCommonSource

namespace TruthCore.Results.Causality.CompleteCauseUnderivedSource
open TruthCore.Causality
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Causality.NecessarilyUnderived
open TruthCore.Causality.WorldSourceRegress
open TruthCore.Causality.SourceForest
open TruthCore.Causality.CompleteCauseContributorCover
open TruthCore.Causality.UnderivedCommonSource

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
  sorry

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
  sorry

end TruthCore.Results.Causality.CompleteCauseUnderivedSource
