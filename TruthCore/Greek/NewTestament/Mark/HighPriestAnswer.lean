import TruthCore.Greek.NewTestament.Mark.ForgivenessAuthority

namespace TruthCore.Greek.NewTestament.Mark.HighPriestAnswer

/-- Participants in the narrated exchange, not independently established historical identities.
The Mark 2 Speaker index lacks the high priest; this local index avoids changing
that bounded vocabulary or treating the high priest as one of its scribes. -/
inductive Speaker | jesus | highPriest deriving DecidableEq

/-- Titles retained as the content of the high priest's question. Neither is
an equation with the case signature's IsGod predicate. -/
inductive Title | messiah | sonOfBlessed deriving DecidableEq

/-- Images predicated of the Son of Man in the future seeing saying. The
coming image alone is not defined as judging or as identity with God. -/
inductive Image | seatedAtRightOfPower | comingWithHeavensClouds deriving DecidableEq

/-- Speech content distinguishes affirmative self-ascription from a prediction
that the addressed hearers will see a titled figure. Holder reuses the spoken
Son-of-Man title from the Mark 2 vocabulary without identifying its referent. -/
inductive Content
  | affirmsSelfAs (title : Title)
  | predictsHearersWillSee
      (holder : ForgivenessAuthority.Holder) (image : Image)
  | chargesPrecedingSpeechAsBlasphemy
  deriving DecidableEq

/-- A local speech extension of the existing narrative, rather than a new
historical signature. The Mark 2 authority assertion has a different action
and scope, so Content here retains the question and prediction's own shape.
`attributes` concerns textual attribution, never actual event truth. -/
structure Narrative where
  prior : ForgivenessAuthority.Narrative
  attributes : Speaker → Content → Bool

/-- Mark 14.61-62, in the complete materialized chapter: the affirmative
answer is read as accepting both titles in the immediately preceding question.
No claim of divine nature or historical utterance is inferred. -/
def ReportedAffirmativeAnswer (n : Narrative) : Prop :=
  n.attributes .jesus (.affirmsSelfAs .messiah) = true ∧
  n.attributes .jesus (.affirmsSelfAs .sonOfBlessed) = true

/-- Mark 14.62 predicts that the addressed hearers will see the Son of Man
seated at Power's right and coming with heaven's clouds. Future seeing is
retained; no fulfillment date, explicit judge predicate, or identity equation
is supplied by this type. -/
def ReportedSonOfManPrediction (n : Narrative) : Prop :=
  n.attributes .jesus (.predictsHearersWillSee .sonOfMan .seatedAtRightOfPower) = true ∧
  n.attributes .jesus (.predictsHearersWillSee .sonOfMan .comingWithHeavensClouds) = true

/-- Mark 14.63-64 attributes the blasphemy charge to the high priest.
It does not assert that the narrator endorses the charge or that it is true. -/
def ReportedBlasphemyReaction (n : Narrative) : Prop :=
  n.attributes .highPriest .chargesPrecedingSpeechAsBlasphemy = true

end TruthCore.Greek.NewTestament.Mark.HighPriestAnswer
