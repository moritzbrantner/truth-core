import TruthCore.Causality.CompleteCauseContributorCover

namespace TruthCore.Results.Causality.CompleteCauseContributorCover
open TruthCore.Logic.Regress (Graph)
open TruthCore.Causality.AtomisticCausalSource (UniqueCausePerEffect)
open TruthCore.Causality.CompleteCauseContributorCover
open TruthCore.Mereology.UniversalFusionBoundary (Composite)

/-- Two causes of the SAME effect contain one another, hence coincide under
ambient parthood antisymmetry. No cause is asserted to exist. -/
theorem uniqueCause {B : Type} [PartialOrder B] (G : Graph B)
    (participants : B → Set B)
    (hProducer : ProducerParticipates G participants)
    (hCover : CompleteCauseCoversContributors G participants) :
    UniqueCausePerEffect G := by
  intro e c d hc hd
  exact le_antisymm (hCover d e hd c (hProducer c e hc))
    (hCover c e hc d (hProducer d e hd))

/-- A complete producer without PROPER parts can cover only itself as a
productive participant. This is the order-theoretic, non-composite sense of
simple; it makes no claim about stronger metaphysical divine simplicity. -/
theorem simple_complete_producer_collapses_participants {B : Type}
    [PartialOrder B] (G : Graph B) (participants : B → Set B)
    (hCover : CompleteCauseCoversContributors G participants)
    (c e : B) (hce : G.edge c e) (hSimple : ¬ Composite c)
    (p : B) (hp : p ∈ participants e) : p = c := by
  have hPart : p ≤ c := hCover c e hce p hp
  rcases lt_or_eq_of_le hPart with hProper | hEqual
  · exact (hSimple ⟨p, hProper⟩).elim
  · exact hEqual

/-- The complementary TWO-PARTICIPANT constraint: if an effect really has
two distinct productive participants, any complete producer covering them
has a proper part. Therefore a non-composite complete producer of that effect
is incompatible with both participants being distinct. The GROUP record is
not thereby reified as a third object or a complete producer. -/
theorem distinct_participants_force_composite_producer {B : Type}
    [PartialOrder B] (G : Graph B) (participants : B → Set B)
    (hCover : CompleteCauseCoversContributors G participants)
    (c e a b : B) (hce : G.edge c e)
    (ha : a ∈ participants e) (hb : b ∈ participants e) (hne : a ≠ b) :
    Composite c := by
  by_contra hSimple
  have hac := simple_complete_producer_collapses_participants
    G participants hCover c e hce hSimple a ha
  have hbc := simple_complete_producer_collapses_participants
    G participants hCover c e hce hSimple b hb
  exact hne (hac.trans hbc.symm)

end TruthCore.Results.Causality.CompleteCauseContributorCover
