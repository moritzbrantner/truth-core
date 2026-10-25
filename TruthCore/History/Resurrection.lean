import TruthCore.Greek.Clement.FirstCorinthians
import TruthCore.Greek.Josephus.Antiquities
import TruthCore.Greek.NewTestament.Acts
import TruthCore.Greek.NewTestament.FirstCorinthians
import TruthCore.Greek.NewTestament.Galatians
import TruthCore.Greek.NewTestament.John
import TruthCore.Greek.NewTestament.Mark
import TruthCore.Greek.NewTestament.Matthew
import TruthCore.Latin.Tacitus.Annals

namespace TruthCore.History.Resurrection
open TruthCore.Case.Catholicism
open TruthCore.Greek.NewTestament.Mark
open TruthCore.Greek.NewTestament.Matthew
open TruthCore.Greek.NewTestament.John
open TruthCore.Greek.NewTestament.Acts
open TruthCore.Greek.NewTestament.FirstCorinthians
open TruthCore.Greek.NewTestament.Galatians
open TruthCore.Greek.Clement.FirstCorinthians
open TruthCore.Greek.Josephus.Antiquities
open TruthCore.Latin.Tacitus.Annals

/-- E0: crucifixion. Death is deliberately separate so the swoon proposal
can accept E0 while contesting the historical death inference. -/
def Crucifixion (s : State) : Prop := s.crucified = true
/-- E1: an appearance proclamation preceded this letter. No number of years
from the crucifixion, authorship date or pre-Pauline formula boundary is encoded. -/
def EarlyProclamation (s : State) : Prop := s.proclaimedBeforeLetter = true
/-- E2: the empty-tomb tradition and Matthew's report of the opposing theft
story. This finding is about traditions, not independently established tomb
emptiness or actual hostile testimony. -/
def TombTradition (s : State) : Prop := MattEmptyTomb s ∧ MattHostileTheftStory s
/-- E3: Cephas and at least one further disciple had experiences interpreted
sincerely as encounters with Jesus. Neither external veridicality nor the
same sensory cause for all reported groups follows from this finding. -/
def SincereExperiences (s : State) : Prop :=
  s.experienced .cephas = true ∧ s.sincere .cephas = true ∧
  s.experienced .disciple = true ∧ s.sincere .disciple = true
/-- E4: Paul's transition from not believing to believing. Self-report and
an interpretation of persecution/preaching support this open finding. -/
def PaulConversion (s : State) : Prop :=
  s.believes .paul .before = false ∧ s.believes .paul .after = true
/-- E5: the particular James identified across texts changed from not
believing to believing. This requires the explicit identity/distributive and
prayer-as-belief reading; none of the reports alone says all this. -/
def JamesConversion (s : State) : Prop :=
  s.believes .james .before = false ∧ s.believes .james .after = true

/-- Distinct open historical reading bridges, never asserted by a source. -/
def CrucifixionBridge (s : State) : Prop := MarkCrucifixionDeath s → Crucifixion s
def EarlyProclamationBridge (s : State) : Prop := PaulReceivedAppearances s → EarlyProclamation s
def SincerityBridge (s : State) : Prop :=
  PaulReceivedAppearances s → JohnDisciplesRejoice s →
  ClementApostolicConviction s → SincereExperiences s
def PaulConversionBridge (s : State) : Prop := PaulPersecutorPreacher s → PaulConversion s
def JamesIdentityBeliefBridge (s : State) : Prop :=
  JohnBrothersUnbelieving s → ActsBrothersPraying s → PaulMetJames s → JamesConversion s

def JesusClaims (s : State) : Prop := s.core.ClaimedDivineAuthority s.core.jesus
def AuthorityVindicated (s : State) : Prop := s.authorityVindicated
def Rose (s : State) : Prop := s.core.RoseFromTheDead s.core.jesus
def DivineCause (s : State) : Prop := s.godCausesWorld
def GodExists (s : State) : Prop := TruthCore.Case.Catholicism.GodExists s.core.IsGod

/-- Catholic historical account, whose causal adequacy remains an open
commitment: actual death, an empty tomb and risen encounter, with the
encounters accounting for Paul's and James's new belief. -/
def CatholicAccount (s : State) : Prop :=
  s.diedOnCross = true ∧ s.tombEmpty = true ∧
  s.mechanism = .risenEncounter ∧ s.paulEncounterCausedBelief = true ∧
  s.jamesEncounterCausedBelief = true
/-- A replacement account conjoins denial of resurrection to a positive
mechanism. It never counts denial alone as explanation. -/
def LegendAccount (s : State) : Prop := ¬ Rose s ∧ s.mechanism = .elaboration
def VisionAccount (s : State) : Prop := ¬ Rose s ∧ s.mechanism = .individualVision
def GroupAccount (s : State) : Prop := ¬ Rose s ∧ s.mechanism = .groupSuggestion
def TheftAccount (s : State) : Prop :=
  ¬ Rose s ∧ s.mechanism = .theftAndVision ∧ s.bodyRemoved = true ∧ s.tombEmpty = true
def SwoonAccount (s : State) : Prop :=
  ¬ Rose s ∧ s.mechanism = .survivorEncounter ∧ s.diedOnCross = false ∧
  s.recovered = true ∧ s.tombEmpty = true

/- Reports/finding extraction is not an argument that any account is true. -/
end TruthCore.History.Resurrection

namespace TruthCore.History.Resurrection

inductive Theory | catholic | legend | hallucination | groupHallucination
  | stolenBody | swoon deriving DecidableEq

/-- Availability is explicit for every shared question, including existence
and causation. Unknown cells are False regardless of unused answer contents. -/
def available (t : Theory) (q : Question) : Bool :=
  match t with
  | .catholic => true
  | .legend | .hallucination | .groupHallucination =>
    match q with
    | .e0 | .e1 | .e2 | .e3 | .e4 | .e5 | .resurrection | .experienceAccount => true
    | .existence | .causation | .jesusClaims | .authorityVindicated
      | .tombAccount | .paulAccount | .jamesAccount => false
  | .stolenBody | .swoon =>
    match q with
    | .e0 | .e1 | .e2 | .e3 | .e4 | .e5 | .resurrection | .experienceAccount
      | .tombAccount => true
    | .existence | .causation | .jesusClaims | .authorityVindicated
      | .paulAccount | .jamesAccount => false

def account (t : Theory) (s : State) : Prop :=
  match t with
  | .catholic => CatholicAccount s
  | .legend => LegendAccount s
  | .hallucination => VisionAccount s
  | .groupHallucination => GroupAccount s
  | .stolenBody => TheftAccount s
  | .swoon => SwoonAccount s

/-- Each claimed answer is a proposition. For rivals the resurrection cell
includes the positive replacement account, not merely denial. A tomb-cause
cell requires emptiness together with removal/recovery; a mechanism label
alone does not answer it. Paul/James causal cells stay unexplained for rivals.
Catholic causal cells are the open causal commitments of CatholicAccount,
not consequences of the textual reports. -/
def answer (t : Theory) (s : State) (q : Question) : Prop :=
  match q with
  | .existence => GodExists s
  | .causation => DivineCause s
  | .jesusClaims => JesusClaims s
  | .authorityVindicated => AuthorityVindicated s
  | .resurrection => if t = .catholic then Rose s else account t s
  | .e0 => Crucifixion s
  | .e1 => EarlyProclamation s
  | .e2 => TombTradition s
  | .e3 => SincereExperiences s
  | .e4 => PaulConversion s
  | .e5 => JamesConversion s
  | .tombAccount | .experienceAccount => account t s
  | .paulAccount => CatholicAccount s
  | .jamesAccount => CatholicAccount s

def answerMap (t : Theory) (s : State) : TruthCore.Metaethics.AnswerMap Question :=
  ⟨fun q => available t q = true, answer t s⟩

def entailedCount (t : Theory) : Nat :=
  (questions.filter (available t)).length

def unexplainedCount (t : Theory) : Nat := questions.length - entailedCount t

/-- Named supplementary historical/causal commitments beyond E0-E5 and the
central resurrection/denial stance: one composite Catholic encounter account;
one elaboration account; one individual-vision account; one group-suggestion
account; theft plus a separate visionary-experience account; survival/recovery.
These counts have no simplicity or probability interpretation. -/
def auxiliaryCount : Theory → Nat
  | .catholic => 1
  | .legend => 1
  | .hallucination => 1
  | .groupHallucination => 1
  | .stolenBody => 2
  | .swoon => 1

/-- Proved coverage of all available answer cells. Kept outside Comparison:
it is a coverage proposition, not a theory bundle. -/
def AnswersHold (t : Theory) (s : State) : Prop :=
  ∀ q, available t q = true → answer t s q

/-- Small model builder for consistency, not an assertion about real history.
Only stage-4 predicates, GodExists, and the divine-cause/authority commitments
are populated. Other stages/Creed articles remain unconstrained by this pilot. -/
def model (m : Mechanism) (raised death empty removed recovered : Bool) : State where
  core := {
    Being := Bool
    IsGod := fun b => b = true
    HasClassicalAttributes := fun _ => True
    RevealsRecognizably := fun _ => True
    jesus := false
    ClaimedDivineAuthority := fun _ => True
    RoseFromTheDead := fun _ => raised = true
    Society := Unit
    catholicChurch := ()
    Founded := fun _ _ => False
    VisibleWithAuthority := fun _ => False
    FoundedAsTeachingAuthority := fun _ _ => False
    DefinitivelyProposesAsRevealed := fun _ _ => False
    creedOneGodFatherAlmightyCreator := False
    creedOneLordJesusChristOnlyBegottenConsubstantial := False
    creedIncarnateOfSpiritAndVirginMary := False
    creedCrucifiedUnderPilateSufferedBuried := False
    creedRoseOnTheThirdDay := False
    creedAscendedSeatedAtRightHand := False
    creedWillComeToJudgeKingdomWithoutEnd := False
    creedHolySpiritLordGiverOfLife := False
    creedOneHolyCatholicApostolicChurch := False
    creedOneBaptismForForgiveness := False
    creedResurrectionOfTheDead := False
    creedLifeOfTheWorldToCome := False }
  reports := fun _ => true
  crucified := true
  diedOnCross := death
  proclaimedBeforeLetter := true
  tombEmpty := empty
  experienced := fun _ => true
  sincere := fun _ => true
  believes := fun _ p => match p with | .before => false | .after => true
  mechanism := m
  bodyRemoved := removed
  recovered := recovered
  godCausesWorld := True
  authorityVindicated := True
  paulEncounterCausedBelief := true
  jamesEncounterCausedBelief := true

end TruthCore.History.Resurrection
