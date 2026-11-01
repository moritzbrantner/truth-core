import TruthCore.Causality.AtomisticCausalSource

/-! Selected-context contributor policies, interpreting Rutten ChapterVII p157
and fn211 (RUTTEN-RENEWED-THEISM-CH7-REPLIES). The supplied family records
ALL productive participants for each effect, including a whole producer, not
only proper partial causes. It is NOT defined as the complete-cause graph's
predecessor set. Necessary background conditions are not automatically
productive participants. Source fidelity and real causal application remain open.
No event ontology, cause existence, fusion formation, causal inheritance or
cross-world identity is introduced. -/
namespace TruthCore.Causality.CompleteCauseContributorCover
open TruthCore.Logic.Regress (Graph)
open TruthCore.Mereology.UniversalFusionBoundary (Covers)

/-- Every complete producer is among the productive participants in its SAME
effect. This broad participant sense includes whole producers; interpreting it
as proper partial causes only would require a different policy. Source p157
speaks of all objects participating in causing, without a proper-part restriction. -/
def ProducerParticipates {B : Type} (G : Graph B)
    (participants : B → Set B) : Prop :=
  ∀ c e, G.edge c e → c ∈ participants e

/-- Every complete cause contains ALL supplied productive participants in its
same effect. This is only the upper-bound consequence of the source's total-sum
reading; it does not characterize every cover as a cause or supply fusion's
no-extra-parts clause. Numerical producer uniqueness is not an input. -/
def CompleteCauseCoversContributors {B : Type} [PartialOrder B] (G : Graph B)
    (participants : B → Set B) : Prop :=
  ∀ c e, G.edge c e → Covers (participants e) c

end TruthCore.Causality.CompleteCauseContributorCover
