import TruthCore.Case.Catholicism.StageThree.Round3ChristChurch

/-! Stage 3-6 round 3 (Christ's claim, his Church and its proposal); every
theorem is conditional on its OPEN hypotheses. -/

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
    JesusClaims n.prior.pilot := by
  sorry

/-- Stage 4 from the Mark 14 route and the pilot's rising. -/
theorem stageFourFromMarkTrial (n : HighPriestAnswer.Narrative) (S : Speech)
    (hAnswer : HighPriestAnswer.ReportedAffirmativeAnswer n)
    (hPrediction : HighPriestAnswer.ReportedSonOfManPrediction n)
    (hBack : MarkTrialSayingsGoBackToJesus n S)
    (hReading : TrialSelfAscriptionIsDivineAuthorityClaim n.prior.pilot.core S)
    (hRose : Rose n.prior.pilot) :
    JesusClaimedDivineAuthorityAndRose n.prior.pilot.core := by
  sorry

/-- Mark 2: the narrative attributes to Jesus the Son of Man's authority to
forgive sins on earth; the saying goes back to Jesus; he used the title of
himself; and self-ascribed authority to forgive sins is a claim to divine
authority. So Jesus claimed divine authority. -/
theorem pilotClaimsFromMarkForgiveness (n : ForgivenessAuthority.Narrative) (S : Speech)
    (hReport : ForgivenessAuthority.ReportedForgivenessAuthority n)
    (hBack : Mark2SayingGoesBackToJesus n S)
    (hSelf : Mark2SonOfManIsSelfReference S)
    (hReading : SelfAscribedForgivenessAuthorityIsDivineAuthorityClaim n.pilot.core S) :
    JesusClaims n.pilot := by
  sorry

/-! ## Attestation -/

/-- If Jesus rose, a God raised him; raising one who claimed divine authority
confirms his mandate. So the resurrection confirms Jesus' mandate. -/
theorem resurrectionConfirmsMandateFromRaising (σ : Signature) (A : Agency σ) (R : Raising σ)
    (hRaised : JesusRaisedByGodIfRose σ R)
    (hConfirms : RaisingAClaimantConfirmsHisMandate σ A R) :
    ResurrectionConfirmsMandate σ A := by
  sorry

/-! ## Commission reports -/

/-- Matthew 28 and John 21 rest on the testimony of those present, and such
testimony is accurate; John 21's commission (shepherding) is governing. -/
theorem commissionReportsFromTestimony (E : Commissioning) (T : Testimony)
    (hRests : Mt28AndJn21RestOnTestimony T)
    (hAccurate : TestimonyOfThosePresentIsAccurate E T) :
    CommissionReportsGoBackToJesus E := by
  sorry

/-- Strength registration: every commission report going back to Jesus entails
the two-report premise. -/
theorem allCommissionReportsEntailTwo (E : Commissioning)
    (hAll : AllCommissionReportsGoBackToJesus E) :
    CommissionReportsGoBackToJesus E := by
  sorry

/-! ## Stage 5: selected Church -/

/-- Selected Church from the commission reports: one of the four governing
reports goes back to Jesus, and each names a governing power. -/
theorem selectedChurchFromCommissionReports (σ : Signature) (E : Commissioning)
    (H : Holding σ) (church : σ.Society → Prop)
    (hReports : CommissionReportsGoBackToJesus E)
    (hFounds : GoverningGiftConstitutesFoundedSociety σ E H)
    (hChurch : HolderOfGivenGoverningPowerIsChurch σ H church) :
    ChristFoundedSelectedChurch σ church := by
  sorry

/-- Selected Church from multiple attestation of the heaven-ratified family,
without any whole report going back to Jesus. -/
theorem selectedChurchFromAttestation (σ : Signature) (E : Commissioning) (T : Tradition)
    (H : Holding σ) (church : σ.Society → Prop)
    (hIndep : JohnCommissionIndependent T)
    (hCrit : HeavenRatifiedAttestationCriterion E T)
    (hFounds : GoverningGiftConstitutesFoundedSociety σ E H)
    (hChurch : HolderOfGivenGoverningPowerIsChurch σ H church) :
    ChristFoundedSelectedChurch σ church := by
  sorry

/-! ## Stage 6 -/

/-- Jesus founded at most one visible society with authority, and the Catholic
Church is one he founded; so every such society is the Catholic Church. -/
theorem christsChurchIsCatholicFromUniqueness (σ : Signature)
    (hOne : JesusFoundedAtMostOneVisibleChurch σ)
    (hCatholic : CatholicChurchIsJesusFoundedVisibleSociety σ) :
    ChristsChurchIsCatholicChurch σ := by
  sorry

/-! ## The Creed proposed -/

/-- The council of 381 taught each article as revealed, and the Catholic
Church definitively proposes what that council taught as revealed. -/
theorem creedProposedFromC381 (σ : Signature) (K : Conciliar)
    (hTaught : C381TaughtEachArticleAsRevealed σ K)
    (hReceived : CatholicChurchProposesWhatC381Taught σ K) :
    CatholicChurchDefinitivelyProposesCreed σ := by
  sorry

/-! ## Controls -/

namespace Controls
open TruthCore.Case.Catholicism.StageThree.Round3ChristChurch.Control

end Controls

/-- The batch controls: a joint witness and an omission model for each premise
of each derivation (22 models). -/
theorem controls : Control.Certificate := by
  sorry

end TruthCore.Results.Case.Catholicism.StageThree.Round3ChristChurch
