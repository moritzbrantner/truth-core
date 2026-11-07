module

public import TruthCore.Case.Catholicism.StageThree.CommissionAttestation
public import TruthCore.Case.Catholicism.StageThree.ChurchDefinitions
public import TruthCore.Greek.NewTestament.Mark.HighPriestAnswer
public import TruthCore.History.Resurrection

/-! Stage 3-6 round 3: Christ's claim, his Church and its proposal (exploration
maps `explorations/jesus-claimed-divine-authority-and-rose.toml`,
`resurrection-confirms-jesus-mandate.toml`, `commission-reports-go-back.toml`,
`christ-founded-selected-church.toml`, `christs-church-is-catholic-church.toml`,
`catholic-church-proposes-creed.toml`, `mandate-covers-founding.toml`).

Analyst formulations, attribution deferred (owner direction 2026-11-05). Every
definition below is an OPEN premise; none is attributed to a source. Where a
pinned claim bears on a node, the corpus records a `supports` relation with a
gap note, never a stating claim.

Each derivation passes through a distinct middle term that this module adds as
a parameter with no axioms:

* `Speech` — what Jesus himself actually said (report-to-event bridges carry
  the textual attributions of Mark 14 and Mark 2 into it);
* `Raising` — who raised whom (the resurrection read as an act of an agent);
* `Testimony` — which commission reports rest on the testimony of those
  present at the commission;
* `Holding` — which society holds which commissioned power;
* `Conciliar` — what the Council of Constantinople (381) taught in its creed
  as belonging to the revealed faith.

Textual attribution and event truth stay distinct (DISAMB-MARK-HIGH-PRIEST-EXCHANGE,
DISAMB-MARK-FORGIVENESS-AUTHORITY, DISAMB-RESURRECTION-PILOT-EVIDENCE): no
inference from a report to an event is made except through a named open
bridge below. -/

@[expose] public section

namespace TruthCore.Case.Catholicism.StageThree.Round3ChristChurch

open TruthCore.Case.Catholicism
open TruthCore.Case.Catholicism.StageThree.DivineFounding
open TruthCore.Case.Catholicism.StageThree.Commissions
open TruthCore.Case.Catholicism.StageThree.CommissionAttestation
open TruthCore.Greek.NewTestament.Mark

/-! ## Stage 4: Jesus' claim from the Mark reports -/

/-- Event vocabulary for Jesus' own speech (DEF-JESUS-SPEECH-EVENT). Unlike the
narrative `attributes` fields, these record what Jesus himself actually said.

* `trialSaid c` — at his hearing before the high priest Jesus himself said the
  content `c` (Mark 14 content type);
* `assertedAuthority a` — Jesus himself asserted the authority content `a`
  (Mark 2 content type);
* `usedOfHimself h` — in asserting authority content about the holder title
  `h`, Jesus used the title of himself.

All three are parameters; no axiom ties them to the reports. -/
structure Speech where
  trialSaid : HighPriestAnswer.Content → Prop
  assertedAuthority : ForgivenessAuthority.AuthorityContent → Prop
  usedOfHimself : ForgivenessAuthority.Holder → Prop

/-- OPEN report-to-event bridge (`STMT-MARK-TRIAL-SAYINGS-GO-BACK-TO-JESUS`):
whatever Mark's narrative attributes to Jesus at the hearing before the high
priest, Jesus himself said. A historicity premise about one scene; it does not
classify what was said. -/
def MarkTrialSayingsGoBackToJesus (n : HighPriestAnswer.Narrative) (S : Speech) : Prop :=
  ∀ c, n.attributes .jesus c = true → S.trialSaid c

/-- OPEN interpretation bridge (`STMT-TRIAL-SELF-ASCRIPTION-IS-DIVINE-AUTHORITY-CLAIM`):
if Jesus himself affirmed that he is the Son of the Blessed and predicted that
his hearers would see the Son of Man seated at the right of Power, he thereby
claimed divine authority. It takes the two sayings together and reads the
Son of Man of the prediction as Jesus himself. Its rival, the delegated
messianic reading (a human Messiah exalted by God without a claim to divine
authority), denies it (DISAMB-MARK-HIGH-PRIEST-EXCHANGE). -/
def TrialSelfAscriptionIsDivineAuthorityClaim (σ : Signature) (S : Speech) : Prop :=
  S.trialSaid (.affirmsSelfAs .sonOfBlessed) →
    S.trialSaid (.predictsHearersWillSee .sonOfMan .seatedAtRightOfPower) →
      σ.ClaimedDivineAuthority σ.jesus

/-- OPEN report-to-event bridge (`STMT-MARK-2-SAYING-GOES-BACK-TO-JESUS`):
whatever authority assertion Mark 2 attributes to Jesus, Jesus himself made. -/
def Mark2SayingGoesBackToJesus (n : ForgivenessAuthority.Narrative) (S : Speech) : Prop :=
  ∀ a, n.attributes .jesus a = true → S.assertedAuthority a

/-- OPEN reference bridge (`STMT-MARK-2-SON-OF-MAN-IS-SELF-REFERENCE`): in
asserting the authority of the Son of Man, Jesus used the title of himself.
Only Mark 2 is meant; no cross-passage identity of the title is asserted. -/
def Mark2SonOfManIsSelfReference (S : Speech) : Prop :=
  S.usedOfHimself .sonOfMan

/-- OPEN interpretation bridge
(`STMT-SELF-ASCRIBED-FORGIVENESS-AUTHORITY-IS-DIVINE-AUTHORITY-CLAIM`): whoever
asserts, of a title he uses of himself, authority to forgive sins on earth
claims divine authority (here: Jesus). Its rival is the delegated-agency
reading of Mark 2.10 (authority given to a human agent), under which the
assertion is a claim to delegated, not divine, authority
(DISAMB-MARK-FORGIVENESS-AUTHORITY). -/
def SelfAscribedForgivenessAuthorityIsDivineAuthorityClaim (σ : Signature) (S : Speech) :
    Prop :=
  ∀ h, S.usedOfHimself h → S.assertedAuthority ⟨h, .forgiveSins, .onEarth⟩ →
    σ.ClaimedDivineAuthority σ.jesus

/-! ## Attestation: the resurrection as an act of God -/

/-- Raising vocabulary (DEF-RAISED-BY): `RaisedBy g x` — `g` raised `x` from
the dead (an agent's act, not merely that `x` rose). A parameter. -/
structure Raising (σ : Signature) where
  RaisedBy : σ.Being → σ.Being → Prop

/-- OPEN premise (`STMT-JESUS-RAISED-BY-GOD-IF-ROSE`): if Jesus rose from the
dead, every God with the classical attributes raised him. Read: a resurrection
exceeds every created power and, given a God, is his act. Its rival accepts the
rising but denies divine agency (an unexplained anomaly). -/
def JesusRaisedByGodIfRose (σ : Signature) (R : Raising σ) : Prop :=
  ∀ g, σ.IsGod g → σ.HasClassicalAttributes g → σ.RoseFromTheDead σ.jesus →
    R.RaisedBy g σ.jesus

/-- OPEN premise (`STMT-RAISING-A-CLAIMANT-CONFIRMS-HIS-MANDATE`): if a God
raised Jesus and Jesus had claimed divine authority, that God, by raising him,
confirms that Jesus holds a mandate from him. Raising is read as a testimonial
sign (`Agency.Confirms`) about the claimant's standing. Supported (not stated)
by Acts 2.22-36. The step from 'claimed divine authority' to 'holds a mandate
from God' is part of this premise. -/
def RaisingAClaimantConfirmsHisMandate (σ : Signature) (A : Agency σ) (R : Raising σ) :
    Prop :=
  ∀ g, σ.IsGod g → R.RaisedBy g σ.jesus → σ.ClaimedDivineAuthority σ.jesus →
    A.Confirms g (A.HoldsMandate σ.jesus g)

/-! ## Commission reports: testimony of those present -/

/-- Testimony vocabulary (DEF-COMMISSION-TESTIMONY): `RestsOnTestimonyOfThosePresent r`
— the report `r` goes back, through its transmission, to the testimony of
disciples present when the commission was given. A parameter. -/
structure Testimony where
  RestsOnTestimonyOfThosePresent : CommissionReport → Prop

/-- OPEN historical premise (`STMT-MT28-AND-JN21-REST-ON-TESTIMONY`): the
reports of Matthew 28.18-20 and John 21.15-17 rest on the testimony of those
present. Only the two reports the target needs are named (weakest version). -/
def Mt28AndJn21RestOnTestimony (T : Testimony) : Prop :=
  T.RestsOnTestimonyOfThosePresent .mt28 ∧ T.RestsOnTestimonyOfThosePresent .jn21

/-- OPEN premise (`STMT-TESTIMONY-OF-THOSE-PRESENT-IS-ACCURATE`): a commission
report resting on the testimony of those present goes back to Jesus: he gave
each power it names. A reliability premise; its rival is the form-critical view
that commission sayings are community formations whatever their channel. -/
def TestimonyOfThosePresentIsAccurate (E : Commissioning) (T : Testimony) : Prop :=
  ∀ r, T.RestsOnTestimonyOfThosePresent r → GoesBackToJesus E r

/-! ## Stage 5: a founded society from a governing commission -/

/-- Holding vocabulary (DEF-SOCIETY-HOLDS-COMMISSIONED-POWER): `HoldsPower c p`
— the society `c` holds the power `p` as given in Jesus' commission. -/
structure Holding (σ : Signature) where
  HoldsPower : σ.Society → Power → Prop

/-- OPEN premise (`STMT-GOVERNING-GIFT-CONSTITUTES-FOUNDED-SOCIETY`): if Jesus
gave a governing power, there is a society that he founded and that holds
that power. Read: authority over members exists only in a society, and giving
it constitutes one. Its rival is the purely personal or charismatic reading of
the commissions (powers given to individuals, no society founded). -/
def GoverningGiftConstitutesFoundedSociety (σ : Signature) (E : Commissioning)
    (H : Holding σ) : Prop :=
  ∀ p, p.Governing = true → E.Gave p → ∃ c, σ.Founded σ.jesus c ∧ H.HoldsPower c p

/-- OPEN calibration premise (`STMT-HOLDER-OF-GIVEN-GOVERNING-POWER-IS-CHURCH`):
a society that holds a governing power given in Jesus' commission is a Church
in the selected sense `church`. A sufficient condition, not a definition. -/
def HolderOfGivenGoverningPowerIsChurch (σ : Signature) (H : Holding σ)
    (church : σ.Society → Prop) : Prop :=
  ∀ c p, p.Governing = true → H.HoldsPower c p → church c

/-! ## Stage 6: one Church, and the Catholic Church founded by Christ -/

/-- OPEN premise (`STMT-JESUS-FOUNDED-AT-MOST-ONE-VISIBLE-CHURCH`): any two
visible societies with authority that Jesus founded are the same society
(identity through time, as in stage 6). Supported (not stated) by Matthew
16.18 'my ekklēsia', singular. Its rival is a plurality of Christ-founded
visible bodies (branch theory). -/
def JesusFoundedAtMostOneVisibleChurch (σ : Signature) : Prop :=
  ∀ c d, σ.Founded σ.jesus c → σ.VisibleWithAuthority c →
    σ.Founded σ.jesus d → σ.VisibleWithAuthority d → c = d

/-- OPEN premise (`STMT-CATHOLIC-CHURCH-IS-JESUS-FOUNDED-VISIBLE-SOCIETY`): the
Catholic Church is a visible society with authority that Jesus founded
(continuity of the society, through its offices, with the one Jesus founded).
Its rivals deny the continuity (a rupture or a refounding). -/
def CatholicChurchIsJesusFoundedVisibleSociety (σ : Signature) : Prop :=
  σ.Founded σ.jesus σ.catholicChurch ∧ σ.VisibleWithAuthority σ.catholicChurch

/-! ## The Creed proposed: Constantinople (381) and its reception -/

/-- Conciliar vocabulary (DEF-C381-TEACHES-AS-REVEALED): `TaughtAsRevealed p`
— the Council of Constantinople (381), in its creed, taught `p` as belonging to
the revealed faith. A parameter over the case's propositions. -/
structure Conciliar where
  TaughtAsRevealed : Prop → Prop

/-- OPEN premise (`STMT-C381-TAUGHT-EACH-ARTICLE-AS-REVEALED`): each of the
twelve Creed articles was taught by the council of 381 as revealed. -/
def C381TaughtEachArticleAsRevealed (σ : Signature) (K : Conciliar) : Prop :=
  ∀ p ∈ CreedArticleList σ, K.TaughtAsRevealed p

/-- OPEN premise (`STMT-CATHOLIC-CHURCH-PROPOSES-WHAT-C381-TAUGHT`): whatever
the council of 381 taught in its creed as revealed, the Catholic Church
definitively proposes as divinely revealed (it receives the council as
ecumenical and its creed as normative). Supported (not stated) by the CDF 1998
commentary and the 2025 reception statement. -/
def CatholicChurchProposesWhatC381Taught (σ : Signature) (K : Conciliar) : Prop :=
  ∀ p, K.TaughtAsRevealed p → σ.DefinitivelyProposesAsRevealed σ.catholicChurch p

/-! ## Controls: one joint witness and omission models

Formal-schema models only (beings and societies are `Bool`; `true` is the God
and the Catholic Church, `false` is Jesus). They show that the batch is not
vacuous and that each premise of each derivation carries weight; they are not
possible worlds of history. -/

namespace Control

/-- A two-being, two-society signature. Jesus' claim is `cda`, his rising
`rose`; Jesus founded society `c` iff `fd c`; `c` is visible with authority iff
`vis c`; the Catholic Church definitively proposes `p` iff `dp p`; every Creed
article is `art`. -/
def sig (cda rose : Prop) (fd vis : Bool → Prop) (dp : Prop → Prop) (art : Prop) :
    Signature where
  Being := Bool
  IsGod b := b = true
  HasClassicalAttributes _ := True
  RevealsRecognizably _ := True
  jesus := false
  ClaimedDivineAuthority _ := cda
  RoseFromTheDead _ := rose
  Society := Bool
  catholicChurch := true
  Founded _ c := fd c
  VisibleWithAuthority c := vis c
  FoundedAsTeachingAuthority _ _ := True
  DefinitivelyProposesAsRevealed _ p := dp p
  creedOneGodFatherAlmightyCreator := art
  creedOneLordJesusChristOnlyBegottenConsubstantial := art
  creedIncarnateOfSpiritAndVirginMary := art
  creedCrucifiedUnderPilateSufferedBuried := art
  creedRoseOnTheThirdDay := art
  creedAscendedSeatedAtRightHand := art
  creedWillComeToJudgeKingdomWithoutEnd := art
  creedHolySpiritLordGiverOfLife := art
  creedOneHolyCatholicApostolicChurch := art
  creedOneBaptismForForgiveness := art
  creedResurrectionOfTheDead := art
  creedLifeOfTheWorldToCome := art

/-- A pilot state over `σ` with every historical field false; only `core` is
used by this batch. -/
def state (σ : Signature) : TruthCore.History.Resurrection.State where
  core := σ
  reports _ := false
  crucified := false
  diedOnCross := false
  proclaimedBeforeLetter := false
  tombEmpty := false
  experienced _ := false
  sincere _ := false
  believes _ _ := false
  mechanism := .risenEncounter
  bodyRemoved := false
  recovered := false
  godCausesWorld := True
  authorityVindicated := True
  paulEncounterCausedBelief := false
  jamesEncounterCausedBelief := false

/-- Mark 2 narrative over `σ` attributing every content to every speaker iff `b`. -/
def mark2 (σ : Signature) (b : Bool) : ForgivenessAuthority.Narrative where
  pilot := state σ
  attributes _ _ := b

/-- Mark 14 narrative over `σ` attributing every content to every speaker iff `b`. -/
def mark14 (σ : Signature) (b : Bool) : HighPriestAnswer.Narrative where
  prior := mark2 σ b
  attributes _ _ := b

/-- Speech with constant fields. -/
def speech (said asserted self : Prop) : Speech where
  trialSaid _ := said
  assertedAuthority _ := asserted
  usedOfHimself _ := self

/-- The standard joint signature: Jesus claimed and rose, founded only the
Catholic Church, which alone is visible, and every article holds and is
proposed. -/
abbrev jσ : Signature := sig True True (fun c => c = true) (fun c => c = true) (fun _ => True) True

/-- Agency of the joint model. -/
def jA : Agency jσ where
  Confirms _ _ := True
  HoldsMandate _ _ := True
  FoundedInMandate _ _ _ := True
  CommissionedToTeach _ _ := True

/-- Raising of the joint model: the God raised Jesus. -/
def jR : Raising jσ := ⟨fun g x => g = true ∧ x = false⟩

/-- Commissioning in which Jesus gave every power. -/
def allGiven : Commissioning := ⟨fun _ => True⟩

/-- Testimony under which the given reports rest on testimony. -/
def testimony (rests : CommissionReport → Prop) : Testimony := ⟨rests⟩

/-- The Catholic Church holds every power. -/
def jH : Holding jσ := ⟨fun c _ => c = true⟩

/-- The council taught every proposition as revealed. -/
def allTaught : Conciliar := ⟨fun _ => True⟩

/-- Joint witness: every premise and conclusion of the batch holds in one model,
with a God, Jesus' claim and rising, the Catholic Church founded by Jesus, and
every Creed article proposed. -/
def JointWitness : Prop :=
  HighPriestAnswer.ReportedAffirmativeAnswer (mark14 jσ true) ∧
  HighPriestAnswer.ReportedSonOfManPrediction (mark14 jσ true) ∧
  MarkTrialSayingsGoBackToJesus (mark14 jσ true) (speech True True True) ∧
  TrialSelfAscriptionIsDivineAuthorityClaim jσ (speech True True True) ∧
  ForgivenessAuthority.ReportedForgivenessAuthority (mark2 jσ true) ∧
  Mark2SayingGoesBackToJesus (mark2 jσ true) (speech True True True) ∧
  Mark2SonOfManIsSelfReference (speech True True True) ∧
  SelfAscribedForgivenessAuthorityIsDivineAuthorityClaim jσ (speech True True True) ∧
  TruthCore.History.Resurrection.JesusClaims (state jσ) ∧
  TruthCore.History.Resurrection.Rose (state jσ) ∧
  JesusClaimedDivineAuthorityAndRose jσ ∧
  JesusRaisedByGodIfRose jσ jR ∧ RaisingAClaimantConfirmsHisMandate jσ jA jR ∧
  ResurrectionConfirmsMandate jσ jA ∧
  Mt28AndJn21RestOnTestimony (testimony fun _ => True) ∧
  TestimonyOfThosePresentIsAccurate allGiven (testimony fun _ => True) ∧
  CommissionReportsGoBackToJesus allGiven ∧
  AllCommissionReportsGoBackToJesus allGiven ∧
  JohnCommissionIndependent allIndependent ∧
  HeavenRatifiedAttestationCriterion allGiven allIndependent ∧
  GoverningGiftConstitutesFoundedSociety jσ allGiven jH ∧
  HolderOfGivenGoverningPowerIsChurch jσ jH (fun c => c = true) ∧
  ChurchDefinitions.ChristFoundedSelectedChurch jσ (fun c => c = true) ∧
  JesusFoundedAtMostOneVisibleChurch jσ ∧ CatholicChurchIsJesusFoundedVisibleSociety jσ ∧
  ChristsChurchIsCatholicChurch jσ ∧ ChristFoundedVisibleChurch jσ ∧
  C381TaughtEachArticleAsRevealed jσ allTaught ∧
  CatholicChurchProposesWhatC381Taught jσ allTaught ∧
  CatholicChurchDefinitivelyProposesCreed jσ

/-- Signature in which Jesus did not claim divine authority (the rest as in
`jσ`). -/
abbrev nσ : Signature := sig False True (fun c => c = true) (fun c => c = true) (fun _ => True) True

/-- Omission models for the Mark 14 derivation: each of its four premises fails
in a model of the other three where Jesus did not claim divine authority. -/
def MarkTrialOmissions : Prop :=
  (∃ n S, ¬ HighPriestAnswer.ReportedAffirmativeAnswer n ∧
    HighPriestAnswer.ReportedSonOfManPrediction n ∧ MarkTrialSayingsGoBackToJesus n S ∧
    TrialSelfAscriptionIsDivineAuthorityClaim n.prior.pilot.core S ∧
    ¬ TruthCore.History.Resurrection.JesusClaims n.prior.pilot) ∧
  (∃ n S, HighPriestAnswer.ReportedAffirmativeAnswer n ∧
    ¬ HighPriestAnswer.ReportedSonOfManPrediction n ∧ MarkTrialSayingsGoBackToJesus n S ∧
    TrialSelfAscriptionIsDivineAuthorityClaim n.prior.pilot.core S ∧
    ¬ TruthCore.History.Resurrection.JesusClaims n.prior.pilot) ∧
  (∃ n S, HighPriestAnswer.ReportedAffirmativeAnswer n ∧
    HighPriestAnswer.ReportedSonOfManPrediction n ∧ ¬ MarkTrialSayingsGoBackToJesus n S ∧
    TrialSelfAscriptionIsDivineAuthorityClaim n.prior.pilot.core S ∧
    ¬ TruthCore.History.Resurrection.JesusClaims n.prior.pilot) ∧
  (∃ n S, HighPriestAnswer.ReportedAffirmativeAnswer n ∧
    HighPriestAnswer.ReportedSonOfManPrediction n ∧ MarkTrialSayingsGoBackToJesus n S ∧
    ¬ TrialSelfAscriptionIsDivineAuthorityClaim n.prior.pilot.core S ∧
    ¬ TruthCore.History.Resurrection.JesusClaims n.prior.pilot)

/-- Omission model for the rising in the stage-4 derivation: every Mark 14
premise holds, Jesus did not rise, and stage 4 fails. -/
def StageFourRoseOmission : Prop :=
  ∃ n S, HighPriestAnswer.ReportedAffirmativeAnswer n ∧
    HighPriestAnswer.ReportedSonOfManPrediction n ∧ MarkTrialSayingsGoBackToJesus n S ∧
    TrialSelfAscriptionIsDivineAuthorityClaim n.prior.pilot.core S ∧
    ¬ TruthCore.History.Resurrection.Rose n.prior.pilot ∧
    ¬ JesusClaimedDivineAuthorityAndRose n.prior.pilot.core

/-- Omission models for the Mark 2 derivation. -/
def Mark2Omissions : Prop :=
  (∃ n S, ¬ ForgivenessAuthority.ReportedForgivenessAuthority n ∧
    Mark2SayingGoesBackToJesus n S ∧ Mark2SonOfManIsSelfReference S ∧
    SelfAscribedForgivenessAuthorityIsDivineAuthorityClaim n.pilot.core S ∧
    ¬ TruthCore.History.Resurrection.JesusClaims n.pilot) ∧
  (∃ n S, ForgivenessAuthority.ReportedForgivenessAuthority n ∧
    ¬ Mark2SayingGoesBackToJesus n S ∧ Mark2SonOfManIsSelfReference S ∧
    SelfAscribedForgivenessAuthorityIsDivineAuthorityClaim n.pilot.core S ∧
    ¬ TruthCore.History.Resurrection.JesusClaims n.pilot) ∧
  (∃ n S, ForgivenessAuthority.ReportedForgivenessAuthority n ∧
    Mark2SayingGoesBackToJesus n S ∧ ¬ Mark2SonOfManIsSelfReference S ∧
    SelfAscribedForgivenessAuthorityIsDivineAuthorityClaim n.pilot.core S ∧
    ¬ TruthCore.History.Resurrection.JesusClaims n.pilot) ∧
  (∃ n S, ForgivenessAuthority.ReportedForgivenessAuthority n ∧
    Mark2SayingGoesBackToJesus n S ∧ Mark2SonOfManIsSelfReference S ∧
    ¬ SelfAscribedForgivenessAuthorityIsDivineAuthorityClaim n.pilot.core S ∧
    ¬ TruthCore.History.Resurrection.JesusClaims n.pilot)

/-- Omission models for the attestation derivation. -/
def AttestationOmissions : Prop :=
  (∃ σ : Signature, ∃ A : Agency σ, ∃ R : Raising σ, ¬ JesusRaisedByGodIfRose σ R ∧
    RaisingAClaimantConfirmsHisMandate σ A R ∧ ¬ ResurrectionConfirmsMandate σ A) ∧
  (∃ σ : Signature, ∃ A : Agency σ, ∃ R : Raising σ, JesusRaisedByGodIfRose σ R ∧
    ¬ RaisingAClaimantConfirmsHisMandate σ A R ∧ ¬ ResurrectionConfirmsMandate σ A)

/-- Omission models for the testimony derivation. -/
def TestimonyOmissions : Prop :=
  (∃ E T, ¬ Mt28AndJn21RestOnTestimony T ∧ TestimonyOfThosePresentIsAccurate E T ∧
    ¬ CommissionReportsGoBackToJesus E) ∧
  (∃ E T, Mt28AndJn21RestOnTestimony T ∧ ¬ TestimonyOfThosePresentIsAccurate E T ∧
    ¬ CommissionReportsGoBackToJesus E)

/-- Omission models for the two selected-Church derivations: without the
commission premise (reports or attestation), without the founding bridge, or
without the Church calibration, no selected Church founded by Jesus exists. -/
def SelectedChurchOmissions : Prop :=
  (∃ σ : Signature, ∃ E : Commissioning, ∃ H : Holding σ, ∃ church : σ.Society → Prop,
    ¬ CommissionReportsGoBackToJesus E ∧ GoverningGiftConstitutesFoundedSociety σ E H ∧
    HolderOfGivenGoverningPowerIsChurch σ H church ∧
    ¬ ChurchDefinitions.ChristFoundedSelectedChurch σ church) ∧
  (∃ σ : Signature, ∃ E : Commissioning, ∃ H : Holding σ, ∃ church : σ.Society → Prop,
    CommissionReportsGoBackToJesus E ∧ ¬ GoverningGiftConstitutesFoundedSociety σ E H ∧
    HolderOfGivenGoverningPowerIsChurch σ H church ∧
    ¬ ChurchDefinitions.ChristFoundedSelectedChurch σ church) ∧
  (∃ σ : Signature, ∃ E : Commissioning, ∃ H : Holding σ, ∃ church : σ.Society → Prop,
    CommissionReportsGoBackToJesus E ∧ GoverningGiftConstitutesFoundedSociety σ E H ∧
    ¬ HolderOfGivenGoverningPowerIsChurch σ H church ∧
    ¬ ChurchDefinitions.ChristFoundedSelectedChurch σ church) ∧
  (∃ σ : Signature, ∃ E : Commissioning, ∃ T : Tradition, ∃ H : Holding σ,
    ∃ church : σ.Society → Prop,
    ¬ JohnCommissionIndependent T ∧ HeavenRatifiedAttestationCriterion E T ∧
    GoverningGiftConstitutesFoundedSociety σ E H ∧
    HolderOfGivenGoverningPowerIsChurch σ H church ∧
    ¬ ChurchDefinitions.ChristFoundedSelectedChurch σ church) ∧
  (∃ σ : Signature, ∃ E : Commissioning, ∃ T : Tradition, ∃ H : Holding σ,
    ∃ church : σ.Society → Prop,
    JohnCommissionIndependent T ∧ ¬ HeavenRatifiedAttestationCriterion E T ∧
    GoverningGiftConstitutesFoundedSociety σ E H ∧
    HolderOfGivenGoverningPowerIsChurch σ H church ∧
    ¬ ChurchDefinitions.ChristFoundedSelectedChurch σ church)

/-- Omission models for the stage-6 derivation. -/
def StageSixOmissions : Prop :=
  (∃ σ : Signature, ¬ JesusFoundedAtMostOneVisibleChurch σ ∧
    CatholicChurchIsJesusFoundedVisibleSociety σ ∧ ¬ ChristsChurchIsCatholicChurch σ) ∧
  (∃ σ : Signature, JesusFoundedAtMostOneVisibleChurch σ ∧
    ¬ CatholicChurchIsJesusFoundedVisibleSociety σ ∧ ¬ ChristsChurchIsCatholicChurch σ)

/-- Omission models for the Creed derivation. -/
def CreedOmissions : Prop :=
  (∃ σ : Signature, ∃ K : Conciliar, ¬ C381TaughtEachArticleAsRevealed σ K ∧
    CatholicChurchProposesWhatC381Taught σ K ∧ ¬ CatholicChurchDefinitivelyProposesCreed σ) ∧
  (∃ σ : Signature, ∃ K : Conciliar, C381TaughtEachArticleAsRevealed σ K ∧
    ¬ CatholicChurchProposesWhatC381Taught σ K ∧ ¬ CatholicChurchDefinitivelyProposesCreed σ)

/-- The batch controls. -/
def Certificate : Prop :=
  JointWitness ∧ MarkTrialOmissions ∧ StageFourRoseOmission ∧ Mark2Omissions ∧
    AttestationOmissions ∧ TestimonyOmissions ∧ SelectedChurchOmissions ∧
    StageSixOmissions ∧ CreedOmissions

end Control

end TruthCore.Case.Catholicism.StageThree.Round3ChristChurch
