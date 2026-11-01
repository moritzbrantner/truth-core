import TruthCore.Causality.CompleteCauseContributorCover

namespace TruthCore.Results.Causality.CompleteCauseContributorCover
open TruthCore.Logic.Regress (Graph)
open TruthCore.Causality.AtomisticCausalSource (UniqueCausePerEffect)
open TruthCore.Causality.CompleteCauseContributorCover

/-- Two causes of the SAME effect contain one another, hence coincide under
ambient parthood antisymmetry. No cause is asserted to exist. -/
theorem uniqueCause {B : Type} [PartialOrder B] (G : Graph B)
    (participants : B → Set B)
    (hProducer : ProducerParticipates G participants)
    (hCover : CompleteCauseCoversContributors G participants) :
    UniqueCausePerEffect G := by
  sorry

end TruthCore.Results.Causality.CompleteCauseContributorCover
