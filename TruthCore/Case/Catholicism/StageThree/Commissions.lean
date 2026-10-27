import TruthCore.Case.Catholicism.StageThree.FoundingScope

/-!
# The reported commissions and the 'institution or message' fork (#357)

The narrow scope premise `MandatedFoundingOfCatholicChurch`
(`STMT-MANDATE-COVERS-JESUS-FOUNDING-OF-CATHOLIC-CHURCH`) says that, if Jesus
holds a mandate from `g` and founded the Catholic Church as a visible society
with authority, he founded it in the exercise of that mandate and commissioned
it to teach. Its rival (Harnack, *History of Dogma* I, ch. II §2, II.7) grants
a mandate but makes it a commission to preach the Gospel.

This module splits the narrow premise along the line where the two part:

1. **Report-to-event** (`CommissionReportsGoBackToJesus`,
   `STMT-COMMISSION-REPORTS-GO-BACK-TO-JESUS`): the commission reported in
   Matthew 28.18-20 goes back to Jesus, and so does at least one of the four
   reported commissions with governing content (Matthew 16.18-19, 18.17-18;
   John 20.21-23, 21.15-17). Which powers each report names is fixed by the
   sourced definition `CommissionReport.powers`; which powers are governing is
   the stipulated classification `Power.Governing`.
2. **Founding in the commissioned apostles** (`ChurchFoundedInCommissionedApostles`,
   `STMT-CHURCH-FOUNDED-IN-COMMISSIONED-APOSTLES`): if Jesus holds a mandate
   from `g` and founded the Catholic Church as a visible society with
   authority, then his giving any governing power to his disciples makes that
   founding a founding in the mandate, and his giving the power to teach is a
   commission of that Church to teach (*Lumen gentium* III §§19, 22).

The derivation is content-sensitive: it goes through only because the
reported powers include a governing one and the power to teach. In a
preaching-only model (`preachingOnlyCommissioning`, the commission Harnack
names; that Harnack denies every other power is not attributed to him), premise
2 holds and premise 1 fails (`preachingOnly_fails_reports`); this depends on
the stipulated distinction of `teach` from `preach`. Premise 2 is strictly
weaker than the narrow premise (`narrow_implies_link` gives one direction, the
first model of `omissionModels` the strictness), but it carries the
institutional content: the conclusion's two parts are its consequents, so the
result applying it is recorded as a transcription (invariant 16). The
'institution or message' fork is split between the two premises, not moved
onto premise 1. A rival may deny premise 2 (the second model of
`omissionModels` satisfies the message rival with every commission
historical); granting premise 2, Jesus' mandate and his founding of the
Catholic Church as a visible society with authority, the rival must deny that
**each** of the four governing commissions goes back to Jesus
(`messageRival_denies_governing_reports`); it may keep Matthew 28.18-20
(`messageRival_compatible_with_mt28`).
`omissionModels` shows both premises needed; `jointModel` shows them jointly
satisfiable with every stage antecedent. These are schema models, not
possible worlds of Christian history.
-/

namespace TruthCore.Case.Catholicism.StageThree.Commissions
open TruthCore.Case.Catholicism
open TruthCore.Case.Catholicism.StageThree.DivineFounding
open TruthCore.Case.Catholicism.StageThree.FoundingScope

/-- Powers named in the five commission reports, together with preaching, the
content Harnack's rival grants (DEF-COMMISSION-EVENT-AND-GOVERNING-POWER).

* `preach` — to proclaim the Gospel (Harnack's "commanded to preach").
* `makeDisciples` — Matthew 28.19 *mathēteusate*.
* `baptize` — Matthew 28.19 *baptizontes*.
* `teach` — Matthew 28.20 *didaskontes ... tērein panta hosa eneteilamēn*.
* `keys` — Matthew 16.19 the keys of the kingdom of heaven (promised to Peter).
* `bindAndLoose` — Matthew 16.19 (Peter) and 18.18 (the disciples addressed).
* `judgeAsChurch` — Matthew 18.17: the *ekklēsia* hears the case, and one who
  refuses to hear it is to be treated as a Gentile and tax collector.
* `forgiveAndRetain` — John 20.23 forgiving and retaining sins.
* `shepherd` — John 21.15-17 feeding and tending Jesus' lambs and sheep. -/
inductive Power
  | preach | makeDisciples | baptize | teach
  | keys | bindAndLoose | judgeAsChurch | forgiveAndRetain | shepherd
  deriving DecidableEq, Repr

/-- A power is *governing* when its exercise is authority over the members of a
society: holding its keys, binding and loosing, judging and excluding,
forgiving and retaining, shepherding the flock. Proclaiming, making disciples,
baptizing and teaching are not classified as governing, so that a commission
consisting only of them is compatible with the message rival. Stipulated
classification (DEF-COMMISSION-EVENT-AND-GOVERNING-POWER), not a source
reading. -/
def Power.Governing : Power → Bool
  | .keys | .bindAndLoose | .judgeAsChurch | .forgiveAndRetain | .shepherd => true
  | .preach | .makeDisciples | .baptize | .teach => false

/-- The five Gospel reports of a commission given by Jesus to his disciples. -/
inductive CommissionReport
  | mt16 | mt18 | mt28 | jn20 | jn21
  deriving DecidableEq, Repr

/-- The powers each report says Jesus gave or, in Matthew 16.19, promised
(DEF-COMMISSION-REPORT-POWERS, sourced by the five report claims). The
recipients differ and are not encoded: Peter (Matthew 16, John 21), the
disciples addressed (Matthew 18.1, 18.18), the eleven (Matthew 28.16), the
disciples gathered without Thomas (John 20.19, 20.24). This is textual
content; that any of it happened is premise 1. -/
def CommissionReport.powers : CommissionReport → List Power
  | .mt16 => [.keys, .bindAndLoose]
  | .mt18 => [.judgeAsChurch, .bindAndLoose]
  | .mt28 => [.makeDisciples, .baptize, .teach]
  | .jn20 => [.forgiveAndRetain]
  | .jn21 => [.shepherd]

/-- Event vocabulary (DEF-COMMISSION-EVENT-AND-GOVERNING-POWER): `Gave p` —
Jesus himself gave, or promised, the power `p` to one or more of his
disciples or to their community (Matthew 18.17 assigns judging to the
*ekklēsia*). It is an uninterpreted parameter, not tied to `σ.jesus` by the
type; its reading as Jesus' act is the definition's. Reports do not fix it. -/
structure Commissioning where
  Gave : Power → Prop

/-- The commission of report `r` goes back to Jesus: he gave (or promised)
each power the report names. The substance of the commission, not its
wording, is meant. -/
def GoesBackToJesus (E : Commissioning) (r : CommissionReport) : Prop :=
  ∀ p ∈ r.powers, E.Gave p

/-- Premise 1, `STMT-COMMISSION-REPORTS-GO-BACK-TO-JESUS`: the commission of
Matthew 28.18-20 goes back to Jesus, and so does the commission of at least
one of Matthew 16.18-19, Matthew 18.17-18, John 20.21-23 and John 21.15-17.
Supported by *Dei Verbum* §19, which asserts more: that the four Gospels
faithfully hand on what Jesus really did and taught
(`all_reports_imply_commission_reports`). -/
def CommissionReportsGoBackToJesus (E : Commissioning) : Prop :=
  GoesBackToJesus E .mt28 ∧
    (GoesBackToJesus E .mt16 ∨ GoesBackToJesus E .mt18 ∨
      GoesBackToJesus E .jn20 ∨ GoesBackToJesus E .jn21)

/-- The stronger reading of *Dei Verbum* §19 restricted to these reports: every
one of the five commissions goes back to Jesus. Not a premise. -/
def AllCommissionReportsGoBackToJesus (E : Commissioning) : Prop :=
  ∀ r, GoesBackToJesus E r

theorem all_reports_imply_commission_reports (E : Commissioning)
    (h : AllCommissionReportsGoBackToJesus E) : CommissionReportsGoBackToJesus E :=
  ⟨h .mt28, Or.inl (h .mt16)⟩

/-- Premise 2, `STMT-CHURCH-FOUNDED-IN-COMMISSIONED-APOSTLES`: for any `g`, if
Jesus holds a mandate from `g` and founded the Catholic Church as a visible
society with authority, then (a) if he gave any governing power to his
disciples, he founded the Catholic Church in the exercise of that mandate, and
(b) if he gave them the power to teach, he commissioned the Catholic Church to
teach. Supported by *Lumen gentium* III §19 (the Lord founded the Church *in
Apostolis*, sent as sharers of his power to make disciples, sanctify and
govern; citing Matthew 28.16-20, John 20.21-23, 21.15-17, Matthew 16.18) and
§22 (Peter as rock and key-bearer, Matthew 16.18-19; pastor of the whole flock,
John 21.15ff; binding and loosing given to the college, Matthew 18.18). That
the council's Church is `catholicChurch` is stage 6's content. The council
asserts one conferral of all these powers on the twelve as a college under
Peter, by the Father's sending; the following are open content of this
premise, not attributed to it: that a **single** governing power suffices,
that a promise counts (Matthew 16.19), that the recipient may be any disciple
or their community, and generality over every mandator `g`. -/
def ChurchFoundedInCommissionedApostles (σ : Signature) (A : Agency σ)
    (E : Commissioning) : Prop :=
  ∀ g, A.HoldsMandate σ.jesus g →
    σ.Founded σ.jesus σ.catholicChurch → σ.VisibleWithAuthority σ.catholicChurch →
      (∀ p, p.Governing = true → E.Gave p →
        A.FoundedInMandate σ.jesus g σ.catholicChurch) ∧
      (E.Gave .teach → A.CommissionedToTeach σ.jesus σ.catholicChurch)

/-- From premise 1: Jesus gave the power to teach, and some governing power.
Each of the four governing reports supplies its own witness. -/
theorem commission_reports_give_teach_and_governing (E : Commissioning)
    (h : CommissionReportsGoBackToJesus E) :
    E.Gave .teach ∧ ∃ p, p.Governing = true ∧ E.Gave p := by
  obtain ⟨h28, hGov⟩ := h
  refine ⟨h28 .teach (.tail _ (.tail _ (.head _))), ?_⟩
  rcases hGov with h16 | h18 | h20 | h21
  · exact ⟨.keys, rfl, h16 .keys (.head _)⟩
  · exact ⟨.judgeAsChurch, rfl, h18 .judgeAsChurch (.head _)⟩
  · exact ⟨.forgiveAndRetain, rfl, h20 .forgiveAndRetain (.head _)⟩
  · exact ⟨.shepherd, rfl, h21 .shepherd (.head _)⟩

/-- Premise 2 is a weakening of the narrow scope premise: the narrow premise
gives both conclusions without any condition on what Jesus gave. The weakening
is strict: the first model of `omissionModels` satisfies premise 2 and not the
narrow premise. -/
theorem narrow_implies_link (σ : Signature) (A : Agency σ) (E : Commissioning)
    (h : MandatedFoundingOfCatholicChurch σ A) :
    ChurchFoundedInCommissionedApostles σ A E :=
  fun g hm hf hv => ⟨fun _ _ _ => (h g hm hf hv).1, fun _ => (h g hm hf hv).2⟩

/-- A preaching-only model: Jesus gave the power to preach and no other. It
contains the commission Harnack names ("commanded to preach the Gospel"); that
no other power was given is the model's, not attributed to Harnack. -/
def preachingOnlyCommissioning : Commissioning where
  Gave p := p = .preach

/-- In the preaching-only model premise 1 fails: Matthew 28's power to teach
(distinct from preaching in `Power`) was not given. -/
theorem preachingOnly_fails_reports :
    ¬ CommissionReportsGoBackToJesus preachingOnlyCommissioning := by
  intro h
  have : Power.teach = Power.preach := h.1 .teach (.tail _ (.tail _ (.head _)))
  exact nomatch this

/-- Where the message rival parts from the case. With premise 2, Jesus'
mandate from `g`, and his founding of the Catholic Church as a visible society
with authority, the rival `MandateCoversOnlyMessage` holds only if **none** of
the four governing commissions goes back to Jesus. -/
theorem messageRival_denies_governing_reports (σ : Signature) (A : Agency σ)
    (E : Commissioning) (g : σ.Being)
    (hLink : ChurchFoundedInCommissionedApostles σ A E)
    (hMandate : A.HoldsMandate σ.jesus g)
    (hFounded : σ.Founded σ.jesus σ.catholicChurch)
    (hVisible : σ.VisibleWithAuthority σ.catholicChurch)
    (hRival : MandateCoversOnlyMessage σ A) :
    ¬ GoesBackToJesus E .mt16 ∧ ¬ GoesBackToJesus E .mt18 ∧
      ¬ GoesBackToJesus E .jn20 ∧ ¬ GoesBackToJesus E .jn21 := by
  have hNo : ∀ p, p.Governing = true → ¬ E.Gave p := fun p hp hg =>
    hRival g σ.catholicChurch hMandate ((hLink g hMandate hFounded hVisible).1 p hp hg)
  exact ⟨fun h => hNo .keys rfl (h .keys (.head _)),
    fun h => hNo .judgeAsChurch rfl (h .judgeAsChurch (.head _)),
    fun h => hNo .forgiveAndRetain rfl (h .forgiveAndRetain (.head _)),
    fun h => hNo .shepherd rfl (h .shepherd (.head _))⟩

/-! ## Schema models -/

/-- Jesus gave exactly the non-governing powers: preaching, making disciples,
baptizing and teaching. -/
def nonGoverningCommissioning : Commissioning where
  Gave p := p.Governing = false

/-- Jesus gave every listed power. -/
def fullCommissioning : Commissioning where
  Gave _ := True

/-- The message rival is compatible with premise 2, with Jesus' mandate, with
his founding of the Catholic Church as a visible society with authority, with
stage 6, and with Matthew 28.18-20 going back to
Jesus: granting premise 2, what it must deny is the four governing
commissions, not the teaching commission. -/
theorem messageRival_compatible_with_mt28 :
    ∃ σ : Signature, ∃ A : Agency σ, ∃ E : Commissioning,
      ChurchFoundedInCommissionedApostles σ A E ∧ MandateCoversOnlyMessage σ A ∧
      (∃ g, A.HoldsMandate σ.jesus g) ∧ σ.Founded σ.jesus σ.catholicChurch ∧
      σ.VisibleWithAuthority σ.catholicChurch ∧ ChristsChurchIsCatholicChurch σ ∧
      GoesBackToJesus E .mt28 := by
  refine ⟨modelSig True, modelAgency True (fun p => p) True False True,
    nonGoverningCommissioning, ?_, ?_, ⟨true, trivial⟩, trivial, trivial,
    fun _ _ _ => rfl, ?_⟩
  · intro _ _ _ _
    refine ⟨fun p hp hg => ?_, fun _ => trivial⟩
    have : true = false := hp.symm.trans hg
    exact Bool.noConfusion this
  · intro _ _ _ h; exact h
  · intro p hp
    cases hp with
    | head => rfl
    | tail _ hp => cases hp with
      | head => rfl
      | tail _ hp => cases hp with
        | head => rfl
        | tail _ hp => nomatch hp

/-- Each premise is needed. Without premise 1 (the preaching-only model), premise 2
holds and the narrow premise fails; without premise 2, every commission goes
back to Jesus and the narrow premise fails. In both models Jesus holds a
mandate and founded the Catholic Church as a visible society with authority. -/
theorem omissionModels :
    (∃ σ : Signature, ∃ A : Agency σ, ∃ E : Commissioning,
      ¬ CommissionReportsGoBackToJesus E ∧ ChurchFoundedInCommissionedApostles σ A E ∧
      ChristFoundedVisibleChurch σ ∧ ¬ MandatedFoundingOfCatholicChurch σ A) ∧
    (∃ σ : Signature, ∃ A : Agency σ, ∃ E : Commissioning,
      CommissionReportsGoBackToJesus E ∧ ¬ ChurchFoundedInCommissionedApostles σ A E ∧
      ChristFoundedVisibleChurch σ ∧ ¬ MandatedFoundingOfCatholicChurch σ A) := by
  refine ⟨⟨modelSig True, modelAgency True (fun p => p) True False True,
      preachingOnlyCommissioning, preachingOnly_fails_reports, ?_, ⟨(), trivial, trivial⟩, ?_⟩,
    ⟨modelSig True, modelAgency True (fun p => p) True False True,
      fullCommissioning, ?_, ?_, ⟨(), trivial, trivial⟩, ?_⟩⟩
  · intro _ _ _ _
    refine ⟨fun p hp hg => ?_, fun hg => nomatch hg⟩
    subst hg
    exact Bool.noConfusion hp
  · intro h; exact (h true trivial trivial trivial).1
  · exact ⟨fun _ _ => trivial, Or.inl fun _ _ => trivial⟩
  · intro h; exact (h true trivial trivial trivial).1 .keys rfl trivial
  · intro h; exact (h true trivial trivial trivial).1

/-- Both premises, every stage antecedent of the founding bridge, and stage 6
are jointly satisfiable, so the derivation is not vacuous. -/
theorem jointModel :
    ∃ σ : Signature, ∃ A : Agency σ, ∃ E : Commissioning,
      CommissionReportsGoBackToJesus E ∧ ChurchFoundedInCommissionedApostles σ A E ∧
      ChristsChurchIsCatholicChurch σ ∧
      GodExists σ.IsGod ∧ GodHasClassicalAttributes σ ∧
      RevelationPossibleAndRecognizable σ ∧ JesusClaimedDivineAuthorityAndRose σ ∧
      ChristFoundedVisibleChurch σ := by
  refine ⟨modelSig True, modelAgency True (fun p => p) True True True,
    fullCommissioning, ⟨fun _ _ => trivial, Or.inl fun _ _ => trivial⟩, ?_, ?_,
    modelSig_antecedents True⟩
  · intro _ _ _ _; exact ⟨fun _ _ _ => trivial, fun _ => trivial⟩
  · intro _ _ _; rfl

end TruthCore.Case.Catholicism.StageThree.Commissions
