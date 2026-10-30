import TruthCore.Case.Catholicism.StageThree.Commissions

/-!
# Multiple attestation of the heaven-ratified power and the message rival (#357)

`Commissions` left the 'institution or message' fork split between the link
premise `ChurchFoundedInCommissionedApostles`
(`STMT-CHURCH-FOUNDED-IN-COMMISSIONED-APOSTLES`) and the historicity of the
governing commissions: a message rival that grants the link premise, Jesus'
mandate and his founding of the Catholic Church as a visible society with
authority must deny each of the four governing commissions
(`Commissions.messageRival_denies_governing_reports`).

This module tests that rival against the strongest historical argument for a
governing commission, multiple attestation, and against the pinned critical
denial.

* **The attested family.** Matthew 16.19 and 18.18 (binding and loosing) and
  John 20.23 (forgiving and retaining sins) share one form: what the disciples
  do on earth is ratified before God (`HeavenRatified`, sourced by the three
  report claims). The family is reported in two strands, Matthean and
  Johannine (`heavenRatified_in_both_strands`), and every power in it is
  governing (`heavenRatified_governing`).
* **Two open historical premises.** `JohnCommissionIndependent`: the
  commission saying of John 20.21-23 is literarily independent of that of
  Matthew 18.17-18 or of Matthew 16.18-19. `HeavenRatifiedAttestationCriterion`:
  if the family is reported in two independent reports, Jesus himself gave
  some power of the family. Neither is sourced yet.
* **Result.** With the link premise, the two premises exclude the message rival
  wherever Jesus holds a mandate and founded the Catholic Church as a visible
  society with authority (`message_rival_excluded_by_attestation`, in
  `Results`). Each premise is needed (`omissionModels`), and they are jointly
  satisfiable with that antecedent (`jointModel`). So a rival that grants the
  link premise, Jesus' mandate and his founding of the Catholic Church as a
  visible society with authority must deny John's independence (from both
  Matthew 18.17-18 and 16.18-19) or the criterion for this family; otherwise
  it denies the link premise, the mandate or the founding (stage 5, Harnack's
  own route).
* **The pinned denial does not reach the family.** Harnack (*History of Dogma*
  I, ch. II §3, note 76) says that the sayings Matthew 16.18 and 18.17 belong
  to a later period. Read at the event level for 18.17 (`JudgingSayingLater`),
  this refutes that Matthew 18.17-18 goes back to Jesus
  (`judgingSayingLater_refutes_mt18`), but is compatible with the
  report-to-event premise, with Matthew 16.18-19 and John 21.15-17 going back
  to Jesus, with John's independence, and with the criterion
  (`judgingSayingLater_compatible`). Matthew 16.18 (the promise to build the
  ekklēsia on the rock) names no power given to a disciple and is not encoded.

These are schema models, not possible worlds of Christian history. Nothing here
decides that the criterion is sound or that John is independent.
-/

namespace TruthCore.Case.Catholicism.StageThree.CommissionAttestation
open TruthCore.Case.Catholicism
open TruthCore.Case.Catholicism.StageThree.DivineFounding
open TruthCore.Case.Catholicism.StageThree.FoundingScope
open TruthCore.Case.Catholicism.StageThree.Commissions

/-- The Gospel strand to which a commission report belongs
(DEF-INDEPENDENT-ATTESTATION). Matthew 16, 18 and 28 are Matthean; John 20 and
21 are Johannine. That two strands are literarily independent is not encoded
here; it is the open premise `JohnCommissionIndependent`. -/
inductive Strand
  | matthean | johannine
  deriving DecidableEq, Repr

/-- The strand of each report (DEF-INDEPENDENT-ATTESTATION). -/
def strandOf : CommissionReport → Strand
  | .mt16 | .mt18 | .mt28 => .matthean
  | .jn20 | .jn21 => .johannine

/-- A power is *heaven-ratified* when its report pairs the disciples' act on
earth with its standing before God (DEF-HEAVEN-RATIFIED-POWER): Matthew 16.19
and 18.18, 'whatever you bind on earth shall be bound in heaven, and whatever
you loose on earth shall be loosed in heaven'; John 20.23, 'whose sins you
forgive, they are forgiven them; whose you retain, they are retained'. The
family is the shared form, not an identity of the two sayings
(DISAMB-ATTESTATION-OF-POWER-AND-FAMILY). -/
def HeavenRatified : Power → Bool
  | .bindAndLoose | .forgiveAndRetain => true
  | .preach | .makeDisciples | .baptize | .teach | .keys | .judgeAsChurch
  | .shepherd => false

/-- Every heaven-ratified power is governing (`Power.Governing`). -/
theorem heavenRatified_governing (p : Power) (h : HeavenRatified p = true) :
    p.Governing = true := by
  cases p <;> first | rfl | exact Bool.noConfusion h

/-- A family `F` of powers is reported in report `r`: `r` names some power in
`F`. A textual fact fixed by `CommissionReport.powers`. -/
def AttestedIn (F : Power → Bool) (r : CommissionReport) : Prop :=
  ∃ p ∈ r.powers, F p = true

/-- The heaven-ratified family is reported in Matthew 16, Matthew 18 and
John 20, and so in both strands. -/
theorem heavenRatified_in_both_strands :
    AttestedIn HeavenRatified .mt16 ∧ AttestedIn HeavenRatified .mt18 ∧
      AttestedIn HeavenRatified .jn20 ∧
      strandOf .mt16 ≠ strandOf .jn20 ∧ strandOf .mt18 ≠ strandOf .jn20 :=
  ⟨⟨.bindAndLoose, .tail _ (.head _), rfl⟩, ⟨.bindAndLoose, .tail _ (.head _), rfl⟩,
    ⟨.forgiveAndRetain, .head _, rfl⟩, Strand.noConfusion, Strand.noConfusion⟩

/-- Literary relations among the reports (DEF-INDEPENDENT-ATTESTATION):
`Independent r₁ r₂` — neither of the two commission sayings derives from the
other, and they share no written source. An uninterpreted parameter; only pairs
of distinct reports matter (`HeavenRatifiedAttestationCriterion`). -/
structure Tradition where
  Independent : CommissionReport → CommissionReport → Prop

/-- Schema tradition: every pair of distinct reports is independent. -/
def allIndependent : Tradition := ⟨fun r₁ r₂ => r₁ ≠ r₂⟩

/-- Open premise `STMT-JOHN-COMMISSION-INDEPENDENT-OF-MATTHEW`: John 20.21-23's
commission saying is independent of Matthew 18.17-18's or of Matthew
16.18-19's. -/
def JohnCommissionIndependent (T : Tradition) : Prop :=
  T.Independent .jn20 .mt18 ∨ T.Independent .jn20 .mt16

/-- Open premise `STMT-HEAVEN-RATIFIED-ATTESTATION-CRITERION`: the criterion of
multiple attestation applied to the heaven-ratified family only. If two
distinct, independent reports each name a heaven-ratified power, then Jesus himself gave
(or promised) some heaven-ratified power. It does not say which one, and it
does not say that any whole report goes back to Jesus. -/
def HeavenRatifiedAttestationCriterion (E : Commissioning) (T : Tradition) : Prop :=
  (∃ r₁ r₂, r₁ ≠ r₂ ∧ T.Independent r₁ r₂ ∧ AttestedIn HeavenRatified r₁ ∧
      AttestedIn HeavenRatified r₂) →
    ∃ p, HeavenRatified p = true ∧ E.Gave p

/-- From the two historical premises: Jesus gave some governing power. -/
theorem attestation_gives_governing (E : Commissioning) (T : Tradition)
    (hIndep : JohnCommissionIndependent T)
    (hCrit : HeavenRatifiedAttestationCriterion E T) :
    ∃ p, p.Governing = true ∧ E.Gave p := by
  obtain ⟨h16, h18, h20, -, -⟩ := heavenRatified_in_both_strands
  have hAnte : ∃ r₁ r₂, r₁ ≠ r₂ ∧ T.Independent r₁ r₂ ∧
      AttestedIn HeavenRatified r₁ ∧ AttestedIn HeavenRatified r₂ := by
    rcases hIndep with h | h
    · exact ⟨.jn20, .mt18, CommissionReport.noConfusion, h, h20, h18⟩
    · exact ⟨.jn20, .mt16, CommissionReport.noConfusion, h, h20, h16⟩
  obtain ⟨p, hp, hGave⟩ := hCrit hAnte
  exact ⟨p, heavenRatified_governing p hp, hGave⟩

/-- Conclusion statement `STMT-MESSAGE-RIVAL-EXCLUDED-GIVEN-FOUNDING`: for any
`g`, if Jesus holds a mandate from `g` and founded the Catholic Church as a
visible society with authority, the message rival `MandateCoversOnlyMessage`
is false. It does not assert the mandate or the founding. -/
def MessageRivalExcludedGivenFounding (σ : Signature) (A : Agency σ) : Prop :=
  ∀ g, A.HoldsMandate σ.jesus g → σ.Founded σ.jesus σ.catholicChurch →
    σ.VisibleWithAuthority σ.catholicChurch → ¬ MandateCoversOnlyMessage σ A

/-- The two historical premises and Matthew 28.18-20's report-to-event content
give, with the link premise, the narrow scope premise. Not a corpus argument:
it would replace the sourced `STMT-COMMISSION-REPORTS-GO-BACK-TO-JESUS` by
unsourced premises (see the attempt record). -/
theorem narrow_from_attestation (σ : Signature) (A : Agency σ) (E : Commissioning)
    (T : Tradition) (h28 : GoesBackToJesus E .mt28)
    (hIndep : JohnCommissionIndependent T)
    (hCrit : HeavenRatifiedAttestationCriterion E T)
    (hLink : ChurchFoundedInCommissionedApostles σ A E) :
    MandatedFoundingOfCatholicChurch σ A := by
  intro g hMandate hFounded hVisible
  obtain ⟨p, hp, hGave⟩ := attestation_gives_governing E T hIndep hCrit
  have hL := hLink g hMandate hFounded hVisible
  exact ⟨hL.1 p hp hGave, hL.2 (h28 .teach (.tail _ (.tail _ (.head _))))⟩

/-- The two historical premises do not give the report-to-event premise: Jesus
may have given Matthew 28's powers and binding and loosing only, so that no
governing report goes back to Jesus as a whole. -/
theorem attestation_not_reports :
    ∃ E : Commissioning, ∃ T : Tradition,
      JohnCommissionIndependent T ∧ HeavenRatifiedAttestationCriterion E T ∧
      ¬ CommissionReportsGoBackToJesus E := by
  refine ⟨⟨fun p => p.Governing = false ∨ p = .bindAndLoose⟩, allIndependent,
    Or.inl CommissionReport.noConfusion, fun _ => ⟨.bindAndLoose, rfl, Or.inr rfl⟩, ?_⟩
  rintro ⟨-, h16 | h18 | h20 | h21⟩
  · exact absurd (h16 .keys (.head _)) (by decide)
  · exact absurd (h18 .judgeAsChurch (.head _)) (by decide)
  · exact absurd (h20 .forgiveAndRetain (.head _)) (by decide)
  · exact absurd (h21 .shepherd (.head _)) (by decide)

/-! ## The pinned critical denial -/

/-- Statement `STMT-MATT-18-17-JUDGING-SAYING-LATER`, the event-level reading of
Harnack's note that the saying Matthew 18.17 belongs to a later period: Jesus
did not give the ekklēsia the power to hear a member's case and exclude one who
refuses it. Harnack's note also dates Matthew 16.18; that saying names no power
given to a disciple and is not encoded. -/
def JudgingSayingLater (E : Commissioning) : Prop :=
  ¬ E.Gave .judgeAsChurch

/-- The denial refutes that Matthew 18.17-18 goes back to Jesus. -/
theorem judgingSayingLater_refutes_mt18 (E : Commissioning)
    (h : JudgingSayingLater E) : ¬ GoesBackToJesus E .mt18 :=
  fun h18 => h (h18 .judgeAsChurch (.head _))

/-- Jesus gave every power except the ekklēsia's judging. -/
def allButJudging : Commissioning where
  Gave p := p ≠ .judgeAsChurch

/-- In `allButJudging` every report other than Matthew 18 goes back to Jesus. -/
theorem allButJudging_goesBack (r : CommissionReport) (hr : r ≠ .mt18) :
    GoesBackToJesus allButJudging r := by
  intro p hp h
  subst h
  cases r with
  | mt18 => exact hr rfl
  | mt16 | mt28 | jn20 | jn21 => exact absurd hp (by decide)

/-- The denial is compatible with the report-to-event premise, with Matthew
16.18-19, John 20.21-23 and John 21.15-17 going back to Jesus, with John's
independence, with the criterion and with the link premise: it reaches only
Matthew 18.17-18. -/
theorem judgingSayingLater_compatible :
    ∃ σ : Signature, ∃ A : Agency σ, ∃ E : Commissioning, ∃ T : Tradition,
      JudgingSayingLater E ∧ CommissionReportsGoBackToJesus E ∧
      GoesBackToJesus E .mt16 ∧ GoesBackToJesus E .jn20 ∧ GoesBackToJesus E .jn21 ∧
      JohnCommissionIndependent T ∧ HeavenRatifiedAttestationCriterion E T ∧
      ChurchFoundedInCommissionedApostles σ A E :=
  ⟨modelSig True, modelAgency True (fun p => p) True True True, allButJudging,
    allIndependent, fun h => h rfl,
    ⟨allButJudging_goesBack .mt28 CommissionReport.noConfusion,
      Or.inl (allButJudging_goesBack .mt16 CommissionReport.noConfusion)⟩,
    allButJudging_goesBack .mt16 CommissionReport.noConfusion,
    allButJudging_goesBack .jn20 CommissionReport.noConfusion,
    allButJudging_goesBack .jn21 CommissionReport.noConfusion,
    Or.inl CommissionReport.noConfusion,
    fun _ => ⟨.forgiveAndRetain, rfl, nofun⟩,
    fun _ _ _ _ => ⟨fun _ _ _ => trivial, fun _ => trivial⟩⟩

/-! ## Schema models -/

/-- No pair of reports independent. -/
def noneIndependent : Tradition := ⟨fun _ _ => False⟩

/-- The antecedent of the conclusion together with the message rival. -/
def RivalWithFounding (σ : Signature) (A : Agency σ) : Prop :=
  (∃ g, A.HoldsMandate σ.jesus g) ∧ σ.Founded σ.jesus σ.catholicChurch ∧
    σ.VisibleWithAuthority σ.catholicChurch ∧ MandateCoversOnlyMessage σ A

/-- The antecedent model: Jesus holds a mandate and founded the Catholic Church
as a visible society with authority, and nothing is founded in the mandate, so
the message rival holds. -/
theorem rivalModel_antecedent :
    RivalWithFounding (modelSig True) (modelAgency True (fun p => p) True False True) :=
  ⟨⟨true, trivial⟩, trivial, trivial, fun _ _ _ h => h⟩

/-- In the antecedent model the conclusion fails. -/
theorem rivalModel_conclusion_fails :
    ¬ MessageRivalExcludedGivenFounding (modelSig True)
      (modelAgency True (fun p => p) True False True) :=
  fun h => h true trivial trivial trivial fun _ _ _ h => h

/-- With only non-governing powers given, the link premise holds whatever
founding in the mandate is. -/
theorem link_nonGoverning (σ : Signature) (A : Agency σ)
    (hTeach : ∀ g, A.HoldsMandate σ.jesus g → σ.Founded σ.jesus σ.catholicChurch →
      σ.VisibleWithAuthority σ.catholicChurch → A.CommissionedToTeach σ.jesus σ.catholicChurch) :
    ChurchFoundedInCommissionedApostles σ A nonGoverningCommissioning := by
  intro g hm hf hv
  refine ⟨fun p hp hg => ?_, fun _ => hTeach g hm hf hv⟩
  have : true = false := hp.symm.trans hg
  exact absurd this Bool.noConfusion

/-- Each premise is needed. In each model Jesus holds a mandate and founded the
Catholic Church as a visible society with authority, the message rival holds,
the other two premises hold and the conclusion fails: (1) without the link
premise, Jesus gave every power and every pair of distinct reports is
independent; (2) without John's independence, no pair is independent and the
criterion holds vacuously; (3) without the criterion, every pair of distinct
reports is independent and Jesus gave only the non-governing powers. -/
theorem omissionModels :
    (∃ σ : Signature, ∃ A : Agency σ, ∃ E : Commissioning, ∃ T : Tradition,
      ¬ ChurchFoundedInCommissionedApostles σ A E ∧ JohnCommissionIndependent T ∧
      HeavenRatifiedAttestationCriterion E T ∧ RivalWithFounding σ A ∧
      ¬ MessageRivalExcludedGivenFounding σ A) ∧
    (∃ σ : Signature, ∃ A : Agency σ, ∃ E : Commissioning, ∃ T : Tradition,
      ChurchFoundedInCommissionedApostles σ A E ∧ ¬ JohnCommissionIndependent T ∧
      HeavenRatifiedAttestationCriterion E T ∧ RivalWithFounding σ A ∧
      ¬ MessageRivalExcludedGivenFounding σ A) ∧
    (∃ σ : Signature, ∃ A : Agency σ, ∃ E : Commissioning, ∃ T : Tradition,
      ChurchFoundedInCommissionedApostles σ A E ∧ JohnCommissionIndependent T ∧
      ¬ HeavenRatifiedAttestationCriterion E T ∧ RivalWithFounding σ A ∧
      ¬ MessageRivalExcludedGivenFounding σ A) := by
  have hLink := link_nonGoverning (modelSig True) (modelAgency True (fun p => p) True False True)
    (fun _ _ _ _ => trivial)
  refine ⟨⟨_, _, fullCommissioning, allIndependent, ?_, Or.inl CommissionReport.noConfusion,
      fun _ => ⟨.bindAndLoose, rfl, trivial⟩, rivalModel_antecedent,
      rivalModel_conclusion_fails⟩,
    ⟨_, _, nonGoverningCommissioning, noneIndependent, hLink, ?_,
      fun ⟨_, _, _, h, _⟩ => h.elim, rivalModel_antecedent, rivalModel_conclusion_fails⟩,
    ⟨_, _, nonGoverningCommissioning, allIndependent, hLink,
      Or.inl CommissionReport.noConfusion, ?_, rivalModel_antecedent,
      rivalModel_conclusion_fails⟩⟩
  · intro h; exact (h true trivial trivial trivial).1 .keys rfl trivial
  · rintro (h | h) <;> exact h
  · intro h
    obtain ⟨p, hp, hg⟩ := h ⟨.jn20, .mt18, CommissionReport.noConfusion,
      CommissionReport.noConfusion, heavenRatified_in_both_strands.2.2.1,
      heavenRatified_in_both_strands.2.1⟩
    have : true = false := (heavenRatified_governing p hp).symm.trans hg
    exact Bool.noConfusion this

/-- The three premises, Jesus' mandate, his founding of the Catholic Church as
a visible society with authority, stage 6 and every stage antecedent of the
founding bridge are jointly satisfiable, so the result is not vacuous. -/
theorem jointModel :
    ∃ σ : Signature, ∃ A : Agency σ, ∃ E : Commissioning, ∃ T : Tradition,
      ChurchFoundedInCommissionedApostles σ A E ∧ JohnCommissionIndependent T ∧
      HeavenRatifiedAttestationCriterion E T ∧
      (∃ g, A.HoldsMandate σ.jesus g) ∧ ChristsChurchIsCatholicChurch σ ∧
      GodExists σ.IsGod ∧ GodHasClassicalAttributes σ ∧
      RevelationPossibleAndRecognizable σ ∧ JesusClaimedDivineAuthorityAndRose σ ∧
      ChristFoundedVisibleChurch σ := by
  refine ⟨modelSig True, modelAgency True (fun p => p) True True True,
    fullCommissioning, allIndependent, ?_, Or.inl CommissionReport.noConfusion,
    fun _ => ⟨.bindAndLoose, rfl, trivial⟩, ⟨true, trivial⟩, ?_,
    modelSig_antecedents True⟩
  · intro _ _ _ _; exact ⟨fun _ _ _ => trivial, fun _ => trivial⟩
  · intro _ _ _; rfl

end TruthCore.Case.Catholicism.StageThree.CommissionAttestation
