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

end TruthCore.Results.Causality.CompleteCauseSourceUniqueness
