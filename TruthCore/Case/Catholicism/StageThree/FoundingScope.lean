import TruthCore.Case.Catholicism.StageThree.DivineFounding

/-!
# The scope of the attested mandate, reduced to one society (#357)

The scope premise `MandatedFoundingWithTeaching`
(`STMT-MANDATE-COVERS-JESUS-FOUNDING-WITH-TEACHING`) of the founding bridge
carries two contested claims at once:

1. *institution, not only message*: the founding of a society was an exercise
   of the mandate, and the society was commissioned to teach;
2. *universal reach*: this holds for **every** visible authoritative society
   in the antecedent `Founded jesus c`, so every such society is the
   commissioned one.

This module separates them. The narrower premise
`MandatedFoundingOfCatholicChurch` keeps only claim 1, for one society, the
Catholic Church. Claim 2 is then supplied by stage 6,
`ChristsChurchIsCatholicChurch` (`STMT-CHRISTS-CHURCH-IS-THE-CATHOLIC-CHURCH`),
which is already a premise of every root route: every visible authoritative
society Jesus founded *is* the Catholic Church. The result
`TruthCore.Results.Case.Catholicism.StageThree.FoundingScope` derives the old
scope premise from the two.

`MandatedFoundingOfCatholicChurch` is strictly weaker than the old scope
premise (`scope_implies_catholic_church_scope`), and neither of the two
premises can be dropped (`omissionModels`); `jointModel` shows them jointly
satisfiable with every stage antecedent. These are schema models, not possible
worlds of Christian history.

The rival "the mandate covered a message, not an institution" (Harnack,
*History of Dogma* I, ch. II §2, II.7: Jesus "did not found a new religious
community" and chose apostles "whom he commanded to preach the Gospel") is
encoded as `MandateCoversOnlyMessage`: no society is founded in the exercise
of the mandate. `messageRival_excludes_scope` shows exactly where it parts
from the case: with Jesus' mandate and the stage-5 founding, it contradicts the
narrower premise. It is not refuted here; which of the two holds is the
historical question of the commission's content.
-/

namespace TruthCore.Case.Catholicism.StageThree.FoundingScope
open TruthCore.Case.Catholicism
open TruthCore.Case.Catholicism.StageThree.DivineFounding

/-- Narrow scope premise `STMT-MANDATE-COVERS-JESUS-FOUNDING-OF-CATHOLIC-CHURCH`:
for any `g`, if Jesus holds a mandate from `g` and founded the Catholic Church
as a visible society with authority, then he founded it in the exercise of
that mandate and commissioned it to teach.

Supported by *Lumen gentium* III §§18-19 (claim
`VATICAN-II-LG-19-CHURCH-FOUNDED-IN-APOSTLES-SENT-WITH-CHRISTS-POWER`): Christ
built the Church by sending the apostles as he was sent by the Father, made
them sharers of his power to make all peoples disciples, and founded the
universal Church in the apostles; and by Matthew 28.18-20. That *Lumen
gentium*'s Church is `catholicChurch` is the claim's reading (§8 *subsistit
in*). Like the old scope premise, `g` ranges over every being from which
Jesus holds a mandate, not only a God. Unlike it, the premise says nothing
about any other society. -/
def MandatedFoundingOfCatholicChurch (σ : Signature) (A : Agency σ) : Prop :=
  ∀ g, A.HoldsMandate σ.jesus g →
    σ.Founded σ.jesus σ.catholicChurch → σ.VisibleWithAuthority σ.catholicChurch →
      A.FoundedInMandate σ.jesus g σ.catholicChurch ∧
        A.CommissionedToTeach σ.jesus σ.catholicChurch

/-- The narrow premise is a weakening of the old scope premise: it is its
instance at the Catholic Church. -/
theorem scope_implies_catholic_church_scope (σ : Signature) (A : Agency σ)
    (h : MandatedFoundingWithTeaching σ A) : MandatedFoundingOfCatholicChurch σ A :=
  fun g hm hf hv => h g hm σ.catholicChurch hf hv

/-- The rival `STMT-JESUS-MANDATE-COVERS-ONLY-MESSAGE`: whatever mandate Jesus
holds, no society is founded in its exercise. Its intended gloss, not encoded
in the type, is that the commission is to preach a message. Read from Harnack, *History of Dogma* I, ch. II §2, II.7 (claim
`HARNACK-HOD-I-II-2-NO-NEW-COMMUNITY-PREACHING-COMMISSION`). -/
def MandateCoversOnlyMessage (σ : Signature) (A : Agency σ) : Prop :=
  ∀ g c, A.HoldsMandate σ.jesus g → ¬ A.FoundedInMandate σ.jesus g c

/-- Where the message rival parts from the case: if Jesus holds a mandate from
`g` and founded the Catholic Church as a visible society with authority, the
rival and the narrow scope premise cannot both hold. So, alongside the other
premises, the rival holds only if the narrow premise, Jesus' mandate, or his
founding of the Catholic Church (stages 5 and 6) fails. -/
theorem messageRival_excludes_scope (σ : Signature) (A : Agency σ) (g : σ.Being)
    (hMandate : A.HoldsMandate σ.jesus g)
    (hFounded : σ.Founded σ.jesus σ.catholicChurch)
    (hVisible : σ.VisibleWithAuthority σ.catholicChurch) :
    ¬ (MandatedFoundingOfCatholicChurch σ A ∧ MandateCoversOnlyMessage σ A) :=
  fun ⟨hScope, hRival⟩ =>
    hRival g σ.catholicChurch hMandate (hScope g hMandate hFounded hVisible).1

/-! ## Schema models: necessity of each premise and joint satisfiability -/

/-- A signature with two beings (`true` is the God, `false` is Jesus) and two
societies (`true` is the Catholic Church), in which every stage predicate
holds, Jesus founded both societies and both are visible with authority. -/
def twoSocietySig : Signature where
  Being := Bool
  IsGod b := b = true
  HasClassicalAttributes _ := True
  RevealsRecognizably _ := True
  jesus := false
  ClaimedDivineAuthority _ := True
  RoseFromTheDead _ := True
  Society := Bool
  catholicChurch := true
  Founded _ _ := True
  VisibleWithAuthority _ := True
  FoundedAsTeachingAuthority _ _ := True
  DefinitivelyProposesAsRevealed _ _ := True
  creedOneGodFatherAlmightyCreator := True
  creedOneLordJesusChristOnlyBegottenConsubstantial := True
  creedIncarnateOfSpiritAndVirginMary := True
  creedCrucifiedUnderPilateSufferedBuried := True
  creedRoseOnTheThirdDay := True
  creedAscendedSeatedAtRightHand := True
  creedWillComeToJudgeKingdomWithoutEnd := True
  creedHolySpiritLordGiverOfLife := True
  creedOneHolyCatholicApostolicChurch := True
  creedOneBaptismForForgiveness := True
  creedResurrectionOfTheDead := True
  creedLifeOfTheWorldToCome := True

/-- In `twoSocietySig` the mandate is held, and only the Catholic Church is
founded in it with a teaching commission. -/
def twoSocietyAgency : Agency twoSocietySig where
  Confirms _ p := p
  HoldsMandate _ _ := True
  FoundedInMandate _ _ c := c = true
  CommissionedToTeach _ c := c = true

/-- Each premise is needed. Without stage 6, a second society Jesus founded is
not the commissioned one, and the old scope premise fails at it. Without the
narrow premise, the Catholic Church is the only society but is not founded in
the mandate. In both models the stage-5 antecedent holds. -/
theorem omissionModels :
    (∃ σ : Signature, ∃ A : Agency σ, MandatedFoundingOfCatholicChurch σ A ∧
      ¬ ChristsChurchIsCatholicChurch σ ∧ ChristFoundedVisibleChurch σ ∧
      ¬ MandatedFoundingWithTeaching σ A) ∧
    (∃ σ : Signature, ∃ A : Agency σ, ¬ MandatedFoundingOfCatholicChurch σ A ∧
      ChristsChurchIsCatholicChurch σ ∧ ChristFoundedVisibleChurch σ ∧
      ¬ MandatedFoundingWithTeaching σ A) := by
  refine ⟨⟨twoSocietySig, twoSocietyAgency, ?_, ?_, ⟨true, trivial, trivial⟩, ?_⟩, ?_⟩
  · intro _ _ _ _; exact ⟨rfl, rfl⟩
  · intro h; exact Bool.false_ne_true (h false trivial trivial)
  · intro h; exact Bool.false_ne_true (h true trivial false trivial trivial).1
  · refine ⟨modelSig True, modelAgency True (fun p => p) True False True,
      ?_, ?_, ⟨(), trivial, trivial⟩, ?_⟩
    · intro h; exact (h true trivial trivial trivial).1
    · intro _ _ _; rfl
    · intro h; exact (h true trivial () trivial trivial).1

/-- The narrow premise, stage 6 and every stage antecedent of the founding
bridge are jointly satisfiable, so the derivation is not vacuous. -/
theorem jointModel :
    ∃ σ : Signature, ∃ A : Agency σ,
      MandatedFoundingOfCatholicChurch σ A ∧ ChristsChurchIsCatholicChurch σ ∧
      GodExists σ.IsGod ∧ GodHasClassicalAttributes σ ∧
      RevelationPossibleAndRecognizable σ ∧ JesusClaimedDivineAuthorityAndRose σ ∧
      ChristFoundedVisibleChurch σ := by
  refine ⟨modelSig True, modelAgency True (fun p => p) True True True,
    ?_, ?_, modelSig_antecedents True⟩
  · intro _ _ _ _; exact ⟨trivial, trivial⟩
  · intro _ _ _; rfl

end TruthCore.Case.Catholicism.StageThree.FoundingScope
