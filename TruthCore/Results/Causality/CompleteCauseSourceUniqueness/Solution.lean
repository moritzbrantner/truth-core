import TruthCore.Causality.CompleteCauseContributorCover
import TruthCore.Causality.SourceForest
import TruthCore.Results.Causality.CompleteCauseContributorCover.Solution
import TruthCore.Results.Causality.SourceForest.Solution

namespace TruthCore.Results.Causality.CompleteCauseSourceUniqueness
open TruthCore.Logic.Regress (Graph)
open TruthCore.Causality.CompleteCauseContributorCover
open TruthCore.Causality.SourceForest

/-- Assembly on ONE complete-production graph. The PartialOrder interprets
object parthood for the contributor policies; connectivity concerns G edges,
not parthood or the participant-membership projection. No source existence,
necessary being, unique constituent, or real grounding application follows. -/
theorem atMostOne {B : Type} [PartialOrder B] (G : Graph B)
    (participants : B → Set B)
    (hProducer : ProducerParticipates G participants)
    (hCover : CompleteCauseCoversContributors G participants)
    (hConnected : WeaklyConnected G) : AtMostOneSource G := by
  have hUnique := TruthCore.Results.Causality.CompleteCauseContributorCover.uniqueCause
    G participants hProducer hCover
  have hPred : UniquePredecessor G := by
    intro a b e ha hb
    exact hUnique e a b ha hb
  exact TruthCore.Results.Causality.SourceForest.atMostOne G hConnected hPred

/-- An ordinary source is also a source of every edge-subgraph on the SAME
carrier. In particular, partial causal edges may exist outside the subgraph:
only complete-production edges are constrained by its cover policies. -/
theorem source_of_supergraph {B : Type} (K G : Graph B)
    (hIncluded : ∀ a b, K.edge a b → G.edge a b)
    (s : B) (hs : G.Source s) : K.Source s := by
  rintro ⟨a, ha⟩
  exact hs ⟨a, hIncluded a s ha⟩

/-- If the complete-production edge-subgraph has at most one source, so does
ordinary causation. No connectivity or unique-predecessor rule is imposed on
the ordinary graph; both graphs range over precisely the same beings. -/
theorem atMostOne_of_subgraph {B : Type} (K G : Graph B)
    (hIncluded : ∀ a b, K.edge a b → G.edge a b)
    (hUnique : AtMostOneSource K) : AtMostOneSource G := by
  intro a b ha hb
  exact hUnique a b
    (source_of_supergraph K G hIncluded a ha)
    (source_of_supergraph K G hIncluded b hb)

/-- Only the complete-production subgraph K needs the contributor-cover
policies and weak connectedness. All other ordinary edges remain partial
or otherwise unclassified causes. The spanning, weakly connected K is an
explicit strong premise, not inferred from ordinary causal connectedness. -/
theorem atMostOne_subgraph {B : Type} [PartialOrder B] (K G : Graph B)
    (participants : B → Set B)
    (hIncluded : ∀ a b, K.edge a b → G.edge a b)
    (hProducer : ProducerParticipates K participants)
    (hCover : CompleteCauseCoversContributors K participants)
    (hConnected : WeaklyConnected K) : AtMostOneSource G :=
  atMostOne_of_subgraph K G hIncluded
    (atMostOne K participants hProducer hCover hConnected)

/-- Source collapse is actually COMPONENT-LOCAL. Two ordinary sources in the
same weak component of the constrained complete-production subgraph must
coincide, even when that subgraph is disconnected on the full carrier. No
well-foundedness, global connectivity or source-existence hypothesis is used.
All ordinary causal edges outside K remain unconstrained. -/
theorem ordinary_sources_eq_of_K_connected_pair {B : Type} [PartialOrder B]
    (K G : Graph B) (participants : B → Set B)
    (hIncluded : ∀ a b, K.edge a b → G.edge a b)
    (hProducer : ProducerParticipates K participants)
    (hCover : CompleteCauseCoversContributors K participants)
    (a b : B) (hPath : Relation.EqvGen K.edge a b)
    (ha : G.Source a) (hb : G.Source b) : a = b := by
  have hUnique := TruthCore.Results.Causality.CompleteCauseContributorCover.uniqueCause
    K participants hProducer hCover
  have hPred : UniquePredecessor K := by
    intro x y e hx hy
    exact hUnique e x y hx hy
  exact TruthCore.Results.Causality.SourceForest.sources_eq_of_connected_pair
    K (TruthCore.Results.Causality.SourceForest.confluent_of_uniquePredecessor K hPred)
    a b hPath
    (source_of_supergraph K G hIncluded a ha)
    (source_of_supergraph K G hIncluded b hb)

/-- CONTRAPOSITIVE: distinct ordinary sources must occupy DIFFERENT weak
components of every such complete-production subgraph. This is a structural
constraint even when no connected spanning subgraph can exist. -/
theorem ordinary_distinct_sources_separate_components {B : Type} [PartialOrder B]
    (K G : Graph B) (participants : B → Set B)
    (hIncluded : ∀ a b, K.edge a b → G.edge a b)
    (hProducer : ProducerParticipates K participants)
    (hCover : CompleteCauseCoversContributors K participants)
    (a b : B) (ha : G.Source a) (hb : G.Source b)
    (hne : a ≠ b) : ¬ Relation.EqvGen K.edge a b := by
  intro hPath
  exact hne (ordinary_sources_eq_of_K_connected_pair K G participants
    hIncluded hProducer hCover a b hPath ha hb)

end TruthCore.Results.Causality.CompleteCauseSourceUniqueness
