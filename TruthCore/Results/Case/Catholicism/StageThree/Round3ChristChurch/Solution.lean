module

public import TruthCore.Case.Catholicism.StageThree.Round3ChristChurch

/-! Stage 3-6 round 3 (Christ's claim, his Church and its proposal); every
theorem is conditional on its OPEN hypotheses. -/

@[expose] public section

namespace TruthCore.Results.Case.Catholicism.StageThree.Round3ChristChurch
open TruthCore.Case.Catholicism
open TruthCore.Case.Catholicism.StageThree.DivineFounding
open TruthCore.Case.Catholicism.StageThree.Commissions
open TruthCore.Case.Catholicism.StageThree.CommissionAttestation
open TruthCore.Case.Catholicism.StageThree.ChurchDefinitions
open TruthCore.Case.Catholicism.StageThree.Round3ChristChurch
open TruthCore.Greek.NewTestament.Mark
open TruthCore.History.Resurrection (JesusClaims Rose)

/-! ## Stage 4 -/

/-- Mark 14: the narrative attributes to Jesus the self-ascription as Son of
the Blessed and the prediction of the Son of Man's session; both sayings go
back to Jesus; read together they claim divine authority. So Jesus claimed
divine authority. -/
theorem pilotClaimsFromMarkTrial (n : HighPriestAnswer.Narrative) (S : Speech)
    (hAnswer : HighPriestAnswer.ReportedAffirmativeAnswer n)
    (hPrediction : HighPriestAnswer.ReportedSonOfManPrediction n)
    (hBack : MarkTrialSayingsGoBackToJesus n S)
    (hReading : TrialSelfAscriptionIsDivineAuthorityClaim n.prior.pilot.core S) :
    JesusClaims n.prior.pilot :=
  hReading (hBack _ hAnswer.2) (hBack _ hPrediction.1)

/-- Stage 4 from the Mark 14 route and the pilot's rising. -/
theorem stageFourFromMarkTrial (n : HighPriestAnswer.Narrative) (S : Speech)
    (hAnswer : HighPriestAnswer.ReportedAffirmativeAnswer n)
    (hPrediction : HighPriestAnswer.ReportedSonOfManPrediction n)
    (hBack : MarkTrialSayingsGoBackToJesus n S)
    (hReading : TrialSelfAscriptionIsDivineAuthorityClaim n.prior.pilot.core S)
    (hRose : Rose n.prior.pilot) :
    JesusClaimedDivineAuthorityAndRose n.prior.pilot.core :=
  ⟨hReading (hBack _ hAnswer.2) (hBack _ hPrediction.1), hRose⟩

/-- Mark 2: the narrative attributes to Jesus the Son of Man's authority to
forgive sins on earth; the saying goes back to Jesus; he used the title of
himself; and self-ascribed authority to forgive sins is a claim to divine
authority. So Jesus claimed divine authority. -/
theorem pilotClaimsFromMarkForgiveness (n : ForgivenessAuthority.Narrative) (S : Speech)
    (hReport : ForgivenessAuthority.ReportedForgivenessAuthority n)
    (hBack : Mark2SayingGoesBackToJesus n S)
    (hSelf : Mark2SonOfManIsSelfReference S)
    (hReading : SelfAscribedForgivenessAuthorityIsDivineAuthorityClaim n.pilot.core S) :
    JesusClaims n.pilot :=
  hReading _ hSelf (hBack _ hReport)

/-! ## Attestation -/

/-- If Jesus rose, a God raised him; raising one who claimed divine authority
confirms his mandate. So the resurrection confirms Jesus' mandate. -/
theorem resurrectionConfirmsMandateFromRaising (σ : Signature) (A : Agency σ) (R : Raising σ)
    (hRaised : JesusRaisedByGodIfRose σ R)
    (hConfirms : RaisingAClaimantConfirmsHisMandate σ A R) :
    ResurrectionConfirmsMandate σ A :=
  fun g hg hAttr _ hClaim hRose => hConfirms g hg (hRaised g hg hAttr hRose) hClaim

/-! ## Commission reports -/

/-- Matthew 28 and John 21 rest on the testimony of those present, and such
testimony is accurate; John 21's commission (shepherding) is governing. -/
theorem commissionReportsFromTestimony (E : Commissioning) (T : Testimony)
    (hRests : Mt28AndJn21RestOnTestimony T)
    (hAccurate : TestimonyOfThosePresentIsAccurate E T) :
    CommissionReportsGoBackToJesus E :=
  ⟨hAccurate _ hRests.1, Or.inr (Or.inr (Or.inr (hAccurate _ hRests.2)))⟩

/-- Strength registration: every commission report going back to Jesus entails
the two-report premise. -/
theorem allCommissionReportsEntailTwo (E : Commissioning)
    (hAll : AllCommissionReportsGoBackToJesus E) :
    CommissionReportsGoBackToJesus E :=
  ⟨hAll .mt28, Or.inl (hAll .mt16)⟩

/-! ## Stage 5: selected Church -/

/-- A governing power Jesus gave makes a founded society that holds it, and
such a society is a Church in the selected sense. -/
theorem selectedChurchOfGoverningGift (σ : Signature) (E : Commissioning) (H : Holding σ)
    (church : σ.Society → Prop)
    (hFounds : GoverningGiftConstitutesFoundedSociety σ E H)
    (hChurch : HolderOfGivenGoverningPowerIsChurch σ H church)
    (hGov : ∃ p, p.Governing = true ∧ E.Gave p) :
    ChristFoundedSelectedChurch σ church := by
  obtain ⟨p, hp, hGave⟩ := hGov
  obtain ⟨c, hc, hHolds⟩ := hFounds p hp hGave
  exact ⟨c, hc, hChurch c p hp hHolds⟩

/-- Selected Church from the commission reports: one of the four governing
reports goes back to Jesus, and each names a governing power. -/
theorem selectedChurchFromCommissionReports (σ : Signature) (E : Commissioning)
    (H : Holding σ) (church : σ.Society → Prop)
    (hReports : CommissionReportsGoBackToJesus E)
    (hFounds : GoverningGiftConstitutesFoundedSociety σ E H)
    (hChurch : HolderOfGivenGoverningPowerIsChurch σ H church) :
    ChristFoundedSelectedChurch σ church :=
  selectedChurchOfGoverningGift σ E H church hFounds hChurch
    (commission_reports_give_teach_and_governing E hReports).2

/-- Selected Church from multiple attestation of the heaven-ratified family,
without any whole report going back to Jesus. -/
theorem selectedChurchFromAttestation (σ : Signature) (E : Commissioning) (T : Tradition)
    (H : Holding σ) (church : σ.Society → Prop)
    (hIndep : JohnCommissionIndependent T)
    (hCrit : HeavenRatifiedAttestationCriterion E T)
    (hFounds : GoverningGiftConstitutesFoundedSociety σ E H)
    (hChurch : HolderOfGivenGoverningPowerIsChurch σ H church) :
    ChristFoundedSelectedChurch σ church :=
  selectedChurchOfGoverningGift σ E H church hFounds hChurch
    (attestation_gives_governing E T hIndep hCrit)

/-! ## Stage 6 -/

/-- Jesus founded at most one visible society with authority, and the Catholic
Church is one he founded; so every such society is the Catholic Church. -/
theorem christsChurchIsCatholicFromUniqueness (σ : Signature)
    (hOne : JesusFoundedAtMostOneVisibleChurch σ)
    (hCatholic : CatholicChurchIsJesusFoundedVisibleSociety σ) :
    ChristsChurchIsCatholicChurch σ :=
  fun c hc hv => hOne c σ.catholicChurch hc hv hCatholic.1 hCatholic.2

/-! ## The Creed proposed -/

/-- The council of 381 taught each article as revealed, and the Catholic
Church definitively proposes what that council taught as revealed. -/
theorem creedProposedFromC381 (σ : Signature) (K : Conciliar)
    (hTaught : C381TaughtEachArticleAsRevealed σ K)
    (hReceived : CatholicChurchProposesWhatC381Taught σ K) :
    CatholicChurchDefinitivelyProposesCreed σ :=
  fun p hp => hReceived p (hTaught p hp)

/-! ## Controls -/

namespace Controls
open TruthCore.Case.Catholicism.StageThree.Round3ChristChurch.Control

theorem jointWitness : JointWitness :=
  ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, fun _ _ => trivial, fun _ _ => trivial, rfl,
    fun _ _ => trivial, trivial, fun _ _ _ => trivial, trivial, trivial,
    ⟨trivial, trivial⟩, fun _ hg _ _ => ⟨hg, rfl⟩, fun _ _ _ _ => trivial,
    fun _ _ _ _ _ _ => trivial, ⟨trivial, trivial⟩, fun _ _ _ _ => trivial,
    ⟨fun _ _ => trivial, Or.inl fun _ _ => trivial⟩, fun _ _ _ => trivial,
    Or.inl CommissionReport.noConfusion, fun _ => ⟨.bindAndLoose, rfl, trivial⟩,
    fun _ _ _ => ⟨true, rfl, rfl⟩, fun _ _ _ h => h, ⟨true, rfl, rfl⟩,
    fun _ _ hc _ hd _ => hc.trans hd.symm, ⟨rfl, rfl⟩, fun _ hc _ => hc,
    ⟨true, rfl, rfl⟩, fun _ _ => trivial, fun _ _ => trivial, fun _ _ => trivial⟩

/-- Mark 14 narrative with a content-dependent attribution `f`. -/
def mark14f (σ : Signature) (f : HighPriestAnswer.Content → Bool) :
    HighPriestAnswer.Narrative where
  prior := mark2 σ true
  attributes _ c := f c

/-- Attributes only the prediction. -/
def onlyPrediction : HighPriestAnswer.Content → Bool
  | .affirmsSelfAs _ => false
  | .predictsHearersWillSee _ _ => true
  | .chargesPrecedingSpeechAsBlasphemy => true

/-- Attributes only the self-ascriptions. -/
def onlyAnswer : HighPriestAnswer.Content → Bool
  | .affirmsSelfAs _ => true
  | .predictsHearersWillSee _ _ => false
  | .chargesPrecedingSpeechAsBlasphemy => false

/-- Speech that says exactly what `f` attributes. -/
def speechOf (f : HighPriestAnswer.Content → Bool) : Speech where
  trialSaid c := f c = true
  assertedAuthority _ := True
  usedOfHimself _ := True

theorem markTrialOmissions : MarkTrialOmissions :=
  ⟨⟨mark14f nσ onlyPrediction, speechOf onlyPrediction,
      fun h => Bool.noConfusion h.1, ⟨rfl, rfl⟩, fun _ h => h,
      fun h _ => Bool.noConfusion h, fun h => h⟩,
    ⟨mark14f nσ onlyAnswer, speechOf onlyAnswer,
      ⟨rfl, rfl⟩, fun h => Bool.noConfusion h.1, fun _ h => h,
      fun _ h => Bool.noConfusion h, fun h => h⟩,
    ⟨mark14 nσ true, speech False True True,
      ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, fun h => h (.affirmsSelfAs .messiah) rfl,
      fun h _ => h, fun h => h⟩,
    ⟨mark14 nσ true, speech True True True,
      ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, fun _ _ => trivial,
      fun h => h trivial trivial, fun h => h⟩⟩

theorem stageFourRoseOmission : StageFourRoseOmission :=
  ⟨mark14 (sig True False (fun c => c = true) (fun c => c = true) (fun _ => True) True) true,
    speech True True True, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, fun _ _ => trivial,
    fun _ _ => trivial, fun h => h, fun h => h.2⟩

theorem mark2Omissions : Mark2Omissions :=
  ⟨⟨mark2 nσ false, speech True False True,
      fun h => Bool.noConfusion h, fun _ h => Bool.noConfusion h, trivial,
      fun _ _ h => h, fun h => h⟩,
    ⟨mark2 nσ true, speech True False True,
      rfl, fun h => h ⟨.sonOfMan, .forgiveSins, .onEarth⟩ rfl, trivial,
      fun _ _ h => h, fun h => h⟩,
    ⟨mark2 nσ true, speech True True False,
      rfl, fun _ _ => trivial, fun h => h, fun _ h _ => h, fun h => h⟩,
    ⟨mark2 nσ true, speech True True True,
      rfl, fun _ _ => trivial, trivial, fun h => h .sonOfMan trivial trivial, fun h => h⟩⟩

/-- Agency of `jσ` whose confirmation relation is constantly `conf`. -/
def agency (conf : Prop) : Agency jσ where
  Confirms _ _ := conf
  HoldsMandate _ _ := True
  FoundedInMandate _ _ _ := True
  CommissionedToTeach _ _ := True

theorem attestationOmissions : AttestationOmissions :=
  ⟨⟨jσ, agency False, ⟨fun _ _ => False⟩,
      fun h => h true rfl trivial trivial, fun _ _ h _ => h,
      fun h => h true rfl trivial trivial trivial trivial⟩,
    ⟨jσ, agency False, ⟨fun _ _ => True⟩,
      fun _ _ _ _ => trivial, fun h => h true rfl trivial trivial,
      fun h => h true rfl trivial trivial trivial trivial⟩⟩

/-- Commissioning in which Jesus gave no power. -/
def noneGiven : Commissioning := ⟨fun _ => False⟩

theorem noneGiven_not_reports : ¬ CommissionReportsGoBackToJesus noneGiven :=
  fun h => h.1 .makeDisciples (.head _)

theorem allGiven_reports : CommissionReportsGoBackToJesus allGiven :=
  ⟨fun _ _ => trivial, Or.inl fun _ _ => trivial⟩

theorem testimonyOmissions : TestimonyOmissions :=
  ⟨⟨noneGiven, testimony fun _ => False, fun h => h.1, fun _ h => h.elim,
      noneGiven_not_reports⟩,
    ⟨noneGiven, testimony fun _ => True, ⟨trivial, trivial⟩,
      fun h => h .mt28 trivial .makeDisciples (.head _), noneGiven_not_reports⟩⟩

/-- Holding that never holds. -/
def noHolding : Holding jσ := ⟨fun _ _ => False⟩

theorem noChurch : ¬ ChristFoundedSelectedChurch jσ (fun _ => False) :=
  fun ⟨_, _, h⟩ => h

theorem selectedChurchOmissions : SelectedChurchOmissions :=
  ⟨⟨jσ, noneGiven, noHolding, fun _ => False, noneGiven_not_reports,
      fun _ _ h => h.elim, fun _ _ _ h => h, noChurch⟩,
    ⟨jσ, allGiven, noHolding, fun _ => False, allGiven_reports,
      fun h => (h .keys rfl trivial).elim fun _ hc => hc.2,
      fun _ _ _ h => h, noChurch⟩,
    ⟨jσ, allGiven, jH, fun _ => False, allGiven_reports,
      fun _ _ _ => ⟨true, rfl, rfl⟩, fun h => h true .keys rfl rfl, noChurch⟩,
    ⟨jσ, noneGiven, noneIndependent, noHolding, fun _ => False,
      fun h => h.elim id id, fun ⟨_, _, _, h, _⟩ => h.elim,
      fun _ _ h => h.elim, fun _ _ _ h => h, noChurch⟩,
    ⟨jσ, noneGiven, allIndependent, noHolding, fun _ => False,
      Or.inl CommissionReport.noConfusion,
      fun h => (h (attestation_antecedent allIndependent
        (Or.inl CommissionReport.noConfusion))).elim fun _ hp => hp.2,
      fun _ _ h => h.elim, fun _ _ _ h => h, noChurch⟩⟩

theorem stageSixOmissions : StageSixOmissions :=
  ⟨⟨sig True True (fun _ => True) (fun _ => True) (fun _ => True) True,
      fun h => Bool.noConfusion (h false true trivial trivial trivial trivial),
      ⟨trivial, trivial⟩, fun h => Bool.noConfusion (h false trivial trivial)⟩,
    ⟨sig True True (fun c => c = false) (fun c => c = false) (fun _ => True) True,
      fun _ _ hc _ hd _ => hc.trans hd.symm, fun h => Bool.noConfusion h.1,
      fun h => Bool.noConfusion (h false rfl rfl)⟩⟩

/-- Signature in which the Catholic Church definitively proposes nothing. -/
abbrev pσ : Signature :=
  sig True True (fun c => c = true) (fun c => c = true) (fun _ => False) True

theorem creedOmissions : CreedOmissions :=
  ⟨⟨pσ, ⟨fun _ => False⟩, fun h => h _ (List.Mem.head _), fun _ h => h,
      fun h => h _ (List.Mem.head _)⟩,
    ⟨pσ, allTaught, fun _ _ => trivial, fun h => h True trivial,
      fun h => h _ (List.Mem.head _)⟩⟩

end Controls

/-- The batch controls: a joint witness and an omission model for each premise
of each derivation (22 models). -/
theorem controls : Control.Certificate :=
  ⟨Controls.jointWitness, Controls.markTrialOmissions, Controls.stageFourRoseOmission,
    Controls.mark2Omissions, Controls.attestationOmissions, Controls.testimonyOmissions,
    Controls.selectedChurchOmissions, Controls.stageSixOmissions, Controls.creedOmissions⟩

end TruthCore.Results.Case.Catholicism.StageThree.Round3ChristChurch
