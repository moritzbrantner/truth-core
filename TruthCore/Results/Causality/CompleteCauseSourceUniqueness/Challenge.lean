import TruthCore.Causality.CompleteCauseContributorCover
import TruthCore.Causality.SourceForest

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
  sorry

end TruthCore.Results.Causality.CompleteCauseSourceUniqueness
