import TruthCore.Greek.NewTestament.John

namespace TruthCore.Greek.NewTestament.John.AbrahamSaying
open TruthCore.History.Resurrection

/-- Narrative participants, not independently established historical identities. -/
inductive Speaker | jesus | formerlyBlindMan deriving DecidableEq

/-- A before-clause retains the subject and coming-to-be verb of John 8.58;
it does not assign a date or an ontological theory to Abraham's beginning. -/
inductive BeforeClause | abrahamCameToBe deriving DecidableEq

/-- Speech forms distinguished by context. `iAm` retains the unresolved
self-predication in 8.58; it is neither a divine-name token nor a declaration
of timeless existence by definition. `identifiesSelfAsFormerBeggar` retains
the supplied complement of the ordinary identification at 9.8-9. -/
inductive Content
  | saysIAmBefore (clause : BeforeClause)
  | saysGodSentMeRatherThanCameFromMyself
  | identifiesSelfAsFormerBeggar
  deriving DecidableEq

/-- Narrated action is distinct from attributed speech and from an inferred
motive: 8.59 does not itself name a blasphemy charge. -/
inductive Action | interlocutorsTakeStonesToThrowAtJesus deriving DecidableEq

/-- A bounded John speech/action extension of the pilot State, whose existing
Reported atoms lack Abraham-clause and self-identification content. This
local type changes no historical signature and defines no report-to-truth rule. -/
structure Narrative where
  state : State
  attributes : Speaker → Content → Bool
  narrates : Action → Bool

/-- John 8.58, read in complete chapters 8-9: the narrative attributes the
before-Abraham/I-am saying to Jesus. Personal preexistence and divine-name
readings require interpretive steps not asserted by this speech-form report. -/
def ReportedAbrahamSaying (n : Narrative) : Prop :=
  n.attributes .jesus (.saysIAmBefore .abrahamCameToBe) = true

/-- John 8.42 attributes to Jesus a denial of coming from himself and an
assertion that God sent him. Commission is reported, not historically proved. -/
def ReportedSendingAssertion (n : Narrative) : Prop :=
  n.attributes .jesus .saysGodSentMeRatherThanCameFromMyself = true

/-- John 8.59 narrates taking stones for throwing at Jesus; no actual impact,
legal verdict, or independently corroborated historical reaction is asserted. -/
def NarratedStoneReaction (n : Narrative) : Prop :=
  n.narrates .interlocutorsTakeStonesToThrowAtJesus = true

/-- John 9.8-9 attributes ordinary self-identification to the formerly blind
man in the dispute over whether he is the former beggar. This control does
not entail that John 8.58 has the same meaning. -/
def ReportedOrdinaryIdentification (n : Narrative) : Prop :=
  n.attributes .formerlyBlindMan .identifiesSelfAsFormerBeggar = true

end TruthCore.Greek.NewTestament.John.AbrahamSaying
