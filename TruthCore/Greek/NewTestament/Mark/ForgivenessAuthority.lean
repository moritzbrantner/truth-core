import TruthCore.History.ResurrectionVocabulary

namespace TruthCore.Greek.NewTestament.Mark.ForgivenessAuthority

/-- Speech participants in the bounded Mark 2 reading, not historical identities. -/
inductive Speaker | jesus | scribes deriving DecidableEq

/-- The title used in the saying is retained without defining it as God or Jesus. -/
inductive Holder | sonOfMan | god deriving DecidableEq

/-- The content is authority to forgive sins, rather than merely to announce a pardon. -/
inductive Action | forgiveSins deriving DecidableEq

/-- The saying's explicit earthly scope; no universal heavenly scope is added. -/
inductive Scope | onEarth deriving DecidableEq

/-- Typed content of an attributed authority assertion. This does not assert that
its holder actually has the authority, or identify the source of that authority. -/
structure AuthorityContent where
  holder : Holder
  action : Action
  scope : Scope
  deriving DecidableEq

/-- Mark-specific speech attribution extends the existing pilot state. The pilot's
`Report` constructors name whole reports without typed speech content, so this
local extension preserves speaker, holder, action and scope without changing the
shared signature. `attributes` records textual attribution, never event truth. -/
structure Narrative where
  pilot : TruthCore.History.Resurrection.State
  attributes : Speaker → AuthorityContent → Bool

/-- Mark 2.10, read in the complete materialized chapter and especially 2.1-12:
the narrative attributes to Jesus the assertion that the Son of Man has authority
to forgive sins on earth. This preserves the title as spoken; identifying its
referent, accepting a historical utterance, and classifying the claim as the
pilot's actual divine-authority claim require further premises. The scribes'
God-alone objection (2.7) is not asserted here as the narrator's own rule. -/
def ReportedForgivenessAuthority (n : Narrative) : Prop :=
  n.attributes .jesus ⟨.sonOfMan, .forgiveSins, .onEarth⟩ = true

end TruthCore.Greek.NewTestament.Mark.ForgivenessAuthority
