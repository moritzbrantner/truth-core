import TruthCore.Comparison.Metaethics
import TruthCore.English.Stevenson.Disagreement

namespace TruthCore.Comparison.Stevenson
open TruthCore.English.VanRoojen TruthCore.English.Stevenson

/-- Refinement of the existing shared comparison vocabulary, with interests,
factual beliefs and attempts to redirect an interlocutor made explicit. -/
structure Sig extends Metaethics.Sig where
  Factual : Sentence → Prop
  Favors : Agent → Sentence → Prop
  Disfavors : Agent → Sentence → Prop
  Believes : Agent → Sentence → Prop
  SeeksChange : Agent → Agent → Sentence → Prop

/-- The original three commitments are retained; the primary account adds
structure and a nonvacuous practical clash under factual agreement. -/
def Theory (s : Sig) : Prop :=
  FreeMoralAssertionExpressesAttitudeReading s.Moral s.Expresses s.free ∧
    MoralSentencesHaveDescriptiveMeaningReading s.Moral s.HasDescriptiveMeaning ∧
    MoralDisagreementInvolvesAttitudeClashReading s.Moral s.Accepts s.Rejects s.ClashInAttitude ∧
    DisagreementReading s.Moral s.Factual s.Favors s.Disfavors s.Believes
      s.SeeksChange s.ClashInAttitude

/-- Satisfiability of the enriched encoded account, including witnessed
interest disagreement under complete agreement on the model's factual domain.
This does not establish the historical theory's truth or explain validity. -/
def FactualAgreementConsistent : Prop := ∃ s : Sig, Theory s
end TruthCore.Comparison.Stevenson
