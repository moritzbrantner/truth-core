import TruthCore.Case.Catholicism.Root
import TruthCore.Metaethics.AnswerMap

/-!
Stage-4 pilot (#223). This is a finite vocabulary for conditional comparison,
not a reconstruction of events from texts. Reports, historical findings and
explanatory commitments are separate. Every causal interpretation is open.
The consistency models establish satisfiability of these limited bundles,
not the truth or completeness of any worldview.
-/
namespace TruthCore.History.Resurrection
open TruthCore.Case.Catholicism

/-- Persons distinguished by this pilot; `disciple` is one further disciple,
not every disciple. `james` names the proposed identification, which the
historical finding requires and the textual reports alone do not establish. -/
inductive Person | cephas | disciple | paul | james deriving DecidableEq
inductive Period | before | after deriving DecidableEq

/-- Contents attributed to texts; constructors never assert their content. -/
inductive Report
  | markCrucifixionDeath | paulReceivedAppearances | mattEmptyTomb
  | mattHostileTheftStory | johnDisciplesRejoice | paulPersecutorPreacher
  | johnBrothersUnbelieving | actsBrothersPraying | paulMetJames
  | josephusJamesStoned | tacitusExecution | clementEndurance
  | clementApostolicConviction | markAuthority | mattUniversalAuthority
  deriving DecidableEq

/-- Proposed accounts, not attributions to modern proponents. Legend here is
elaboration of sincere experience into bodily-resurrection narrative; it is
not the already incompatible thesis that no appearance proclamation preceded
the Corinthian letter. Group suggestion and individual vision are distinct.
A mechanism label states which account is proposed, not its adequacy. -/
inductive Mechanism
  | risenEncounter | elaboration | individualVision | groupSuggestion
  | theftAndVision | survivorEncounter deriving DecidableEq

/-- Question IDs in the one shared question set. The six E-items remain
separate from questions about their causes and from metaphysical questions. -/
inductive Question
  | existence | causation | jesusClaims | authorityVindicated | resurrection
  | e0 | e1 | e2 | e3 | e4 | e5
  | tombAccount | experienceAccount | paulAccount | jamesAccount
  deriving DecidableEq

def questions : List Question :=
  [.existence, .causation, .jesusClaims, .authorityVindicated, .resurrection,
   .e0, .e1, .e2, .e3, .e4, .e5, .tombAccount, .experienceAccount,
   .paulAccount, .jamesAccount]

/-- Shared parameters. `core` reuses the existing case signature; no new
per-file interpretation of God, authority or resurrection replaces it.
Booleans encode decidable finite historical assertions in a model. They do
not encode epistemic certainty. -/
structure State where
  core : Signature
  reports : Report → Bool
  crucified : Bool
  diedOnCross : Bool
  proclaimedBeforeLetter : Bool
  tombEmpty : Bool
  experienced : Person → Bool
  sincere : Person → Bool
  believes : Person → Period → Bool
  mechanism : Mechanism
  bodyRemoved : Bool
  recovered : Bool
  godCausesWorld : Prop
  authorityVindicated : Prop
  paulEncounterCausedBelief : Bool
  jamesEncounterCausedBelief : Bool

/-- Textual attribution only. Exact locators/interpretations are in claims. -/
def Reported (s : State) (r : Report) : Prop := s.reports r = true

end TruthCore.History.Resurrection
