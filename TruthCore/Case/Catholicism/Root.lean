/-!
Root node and skeleton vocabulary for the case that Catholicism is true
(epic #143, issue #156).

This module is a modeling layer, not a source reading. Every proposition below
is an independent corpus statement. The stage conclusions and the bridge
premises are *open premises*: they enter results only as hypotheses, never as
axioms, and they are defended (or not) by separate sourced arguments.

The formalization is deliberately weak. Apart from a little first-order
structure for the ecclesial step (a type of societies, the Catholic Church as
one of them, and identity between societies), every stage conclusion and every
Creed article is an uninterpreted proposition supplied by the `Signature`.
Nothing here defines the root in terms of the stages: the root is phase 1 of
issue #156, (A) the Catholic Church is the teaching authority founded by God,
and (B) the articles of the Nicene-Constantinopolitan Creed. The stages reach
the root only through the separate bridge premises.

Source status: the Creed articles are read from the pinned Greek witness
`CREED-C381` (claims `CREED-C381-ART-01` to `-12`). Dei Filius ch. 3, the
source of (A) and of the bridge premises, has no pinned witness yet (candidate
`VATICAN-I-DEI-FILIUS-CH3`), so those statements carry no claims.
-/

namespace TruthCore.Case.Catholicism

universe u

/-- The shared signature of the skeleton. All fields are parameters; none is
given a definition or an axiom.

* `Being`, `IsGod` — beings and the predicate "is God" (the God of classical
  theism, not merely what is called God).
* `Society`, `catholicChurch` — societies of people, and the Catholic Church
  as one of them (identified historically as the society in communion with the
  bishop of Rome).
* `ChristFoundedAsVisibleChurch c` — Christ founded `c` as a visible, enduring
  society with an authority structure.
* `GodFoundedTeachingAuthority c` — `c` is a teaching authority founded by God.
* `DefinitivelyProposesAsRevealed c p` — `c` definitively proposes `p` to be
  believed as divinely revealed (by solemn judgment or ordinary and universal
  magisterium).
* the stage atoms 2-4 and the twelve Creed articles, as uninterpreted
  propositions.
-/
structure Signature where
  Being : Type u
  IsGod : Being → Prop
  Society : Type u
  catholicChurch : Society
  ChristFoundedAsVisibleChurch : Society → Prop
  GodFoundedTeachingAuthority : Society → Prop
  DefinitivelyProposesAsRevealed : Society → Prop → Prop
  godHasClassicalAttributes : Prop
  revelationPossibleAndRecognizable : Prop
  jesusClaimedDivineAuthorityAndRose : Prop
  creedOneGodFatherAlmightyCreator : Prop
  creedOneLordJesusChristOnlyBegottenConsubstantial : Prop
  creedIncarnateOfSpiritAndVirginMary : Prop
  creedCrucifiedUnderPilateSufferedBuried : Prop
  creedRoseOnTheThirdDay : Prop
  creedAscendedSeatedAtRightHand : Prop
  creedWillComeToJudgeKingdomWithoutEnd : Prop
  creedHolySpiritLordGiverOfLife : Prop
  creedOneHolyCatholicApostolicChurch : Prop
  creedOneBaptismForForgiveness : Prop
  creedResurrectionOfTheDead : Prop
  creedLifeOfTheWorldToCome : Prop

/-! ## Creed articles (B)

Each article is an uninterpreted proposition. The division into twelve
articles follows the clause structure of the Greek text (see the `CREED-C381`
source notes). The Greek text has no Filioque; the Latin Catholic form is a
separate candidate (`CREED-C381-FILIOQUE`).
-/

/-- Art. 1: there is one God, the Father almighty, maker of heaven and earth,
of all things visible and invisible (*Πιστεύομεν εἰς ἕνα Θεὸν Πατέρα
παντοκράτορα*). Source: Creed of Constantinople (381), art. 1. -/
def CreedOneGodFatherAlmightyCreator (σ : Signature) : Prop :=
  σ.creedOneGodFatherAlmightyCreator

/-- Art. 2: there is one Lord Jesus Christ, the only-begotten Son of God,
begotten of the Father before all ages, true God from true God, begotten not
made, consubstantial with the Father, through whom all things came to be
(*Καὶ εἰς ἕνα κύριον Ἰησοῦν Χριστόν*). Source: Creed of Constantinople (381),
art. 2. -/
def CreedOneLordJesusChristOnlyBegottenConsubstantial (σ : Signature) : Prop :=
  σ.creedOneLordJesusChristOnlyBegottenConsubstantial

/-- Art. 3: for us and for our salvation he came down from heaven, was
incarnate of the Holy Spirit and the Virgin Mary, and became man (*τὸν δι' ἡμᾶς
τοὺς ἀνθρώπους*). Source: Creed of Constantinople (381), art. 3. -/
def CreedIncarnateOfSpiritAndVirginMary (σ : Signature) : Prop :=
  σ.creedIncarnateOfSpiritAndVirginMary

/-- Art. 4: he was crucified for us under Pontius Pilate, suffered and was
buried (*σταυρωθέντα τε ὑπὲρ ἡμῶν*). Source: Creed of Constantinople (381),
art. 4. -/
def CreedCrucifiedUnderPilateSufferedBuried (σ : Signature) : Prop :=
  σ.creedCrucifiedUnderPilateSufferedBuried

/-- Art. 5: he rose on the third day according to the Scriptures (*καὶ
ἀναστάντα τῇ τρίτῃ ἡμέρᾳ*). Source: Creed of Constantinople (381), art. 5. -/
def CreedRoseOnTheThirdDay (σ : Signature) : Prop :=
  σ.creedRoseOnTheThirdDay

/-- Art. 6: he ascended into heaven and is seated at the right hand of the
Father (*καὶ ἀνελθόντα εἰς τοὺς οὐρανούς*). Source: Creed of Constantinople
(381), art. 6. -/
def CreedAscendedSeatedAtRightHand (σ : Signature) : Prop :=
  σ.creedAscendedSeatedAtRightHand

/-- Art. 7: he will come again in glory to judge the living and the dead, and
his kingdom will have no end (*καὶ πάλιν ἐρχόμενον μετὰ δόξης*). Source: Creed
of Constantinople (381), art. 7. -/
def CreedWillComeToJudgeKingdomWithoutEnd (σ : Signature) : Prop :=
  σ.creedWillComeToJudgeKingdomWithoutEnd

/-- Art. 8: there is the Holy Spirit, the Lord and giver of life, who proceeds
from the Father, who with the Father and the Son is worshipped and glorified,
and who spoke through the prophets (*Καὶ εἰς τὸ Πνεῦμα τὸ Ἅγιον*). Source:
Creed of Constantinople (381), art. 8. -/
def CreedHolySpiritLordGiverOfLife (σ : Signature) : Prop :=
  σ.creedHolySpiritLordGiverOfLife

/-- Art. 9: there is one, holy, catholic and apostolic Church (*εἰς μίαν,
ἁγίαν, καθολικὴν καὶ ἀποστολικὴν ἐκκλησίαν*). Not identified with stage 6 or
with `catholicChurch`: the article does not itself say which society that
Church is. Source: Creed of Constantinople (381), art. 9. -/
def CreedOneHolyCatholicApostolicChurch (σ : Signature) : Prop :=
  σ.creedOneHolyCatholicApostolicChurch

/-- Art. 10: there is one baptism for the forgiveness of sins (*ὁμολογοῦμεν ἓν
βάπτισμα*). Source: Creed of Constantinople (381), art. 10. -/
def CreedOneBaptismForForgiveness (σ : Signature) : Prop :=
  σ.creedOneBaptismForForgiveness

/-- Art. 11: the dead will rise (*προσδοκοῦμεν ἀνάστασιν νεκρῶν*). Source:
Creed of Constantinople (381), art. 11. -/
def CreedResurrectionOfTheDead (σ : Signature) : Prop :=
  σ.creedResurrectionOfTheDead

/-- Art. 12: there will be the life of the world to come (*καὶ ζωὴν τοῦ
μέλλοντος αἰῶνος*). Source: Creed of Constantinople (381), art. 12. -/
def CreedLifeOfTheWorldToCome (σ : Signature) : Prop :=
  σ.creedLifeOfTheWorldToCome

/-- The twelve articles of the Creed, as listed in `Signature`. -/
def CreedArticleList (σ : Signature) : List Prop :=
  [σ.creedOneGodFatherAlmightyCreator,
   σ.creedOneLordJesusChristOnlyBegottenConsubstantial,
   σ.creedIncarnateOfSpiritAndVirginMary,
   σ.creedCrucifiedUnderPilateSufferedBuried,
   σ.creedRoseOnTheThirdDay,
   σ.creedAscendedSeatedAtRightHand,
   σ.creedWillComeToJudgeKingdomWithoutEnd,
   σ.creedHolySpiritLordGiverOfLife,
   σ.creedOneHolyCatholicApostolicChurch,
   σ.creedOneBaptismForForgiveness,
   σ.creedResurrectionOfTheDead,
   σ.creedLifeOfTheWorldToCome]

/-- (B) Every article of the Nicene-Constantinopolitan Creed holds. -/
def CreedArticlesHold (σ : Signature) : Prop :=
  ∀ p ∈ CreedArticleList σ, p

/-! ## Root -/

/-- (A) The Catholic Church is the teaching authority founded by God.

Phase-1 component (A) of issue #156, after Vatican I, *Dei Filius* ch. 3 (the
Church as a motive of credibility and witness of its divine mission). No
pinned witness: candidate `VATICAN-I-DEI-FILIUS-CH3`. -/
def CatholicChurchIsGodFoundedTeachingAuthority (σ : Signature) : Prop :=
  σ.GodFoundedTeachingAuthority σ.catholicChurch

/-- Root `STMT-CATHOLICISM-TRUE`, phase 1: (A) and (B).

The extension to the full list of defined dogmas (phase 2, after Ott and
Denzinger) is candidate `CATHOLICISM-ROOT-PHASE-2-DOGMAS`, not part of this
definition. -/
def CatholicismTrue (σ : Signature) : Prop :=
  CatholicChurchIsGodFoundedTeachingAuthority σ ∧ CreedArticlesHold σ

/-! ## Stage conclusions (open premises) -/

/-- Stage 1: God exists. Shared with `stageOneFromPrimaVia`, which reaches it
from the prima via plus the open gap premises. -/
def GodExists {Being : Sort u} (IsGod : Being → Prop) : Prop :=
  ∃ g, IsGod g

/-- Stage 2: God has the classical divine attributes: simplicity, perfection,
goodness, infinity, immutability, eternity, unity, intellect and will (ST I
qq.3-26). An uninterpreted proposition. -/
def GodHasClassicalAttributes (σ : Signature) : Prop :=
  σ.godHasClassicalAttributes

/-- Stage 3: divine revelation is possible and can be recognized as such by
external signs (motives of credibility). An uninterpreted proposition. -/
def RevelationPossibleAndRecognizable (σ : Signature) : Prop :=
  σ.revelationPossibleAndRecognizable

/-- Stage 4: Jesus claimed to speak and act with divine authority, and he rose
from the dead. An uninterpreted proposition; per the owner decision on #143,
historical findings enter later as their own sourced premises. -/
def JesusClaimedDivineAuthorityAndRose (σ : Signature) : Prop :=
  σ.jesusClaimedDivineAuthorityAndRose

/-- Stage 5: Christ founded a visible, enduring Church with an authority
structure. -/
def ChristFoundedVisibleChurch (σ : Signature) : Prop :=
  ∃ c, σ.ChristFoundedAsVisibleChurch c

/-- Stage 6: that Church is the Catholic Church: every society Christ founded
as a visible Church is the Catholic Church. Identity of societies is
historical identity through time, modeled as equality in `Society`. -/
def ChristsChurchIsCatholicChurch (σ : Signature) : Prop :=
  ∀ c, σ.ChristFoundedAsVisibleChurch c → c = σ.catholicChurch

/-! ## Bridge premises (open premises) -/

/-- Bridge: if God exists and has the classical attributes, revelation is
possible and recognizable, and Jesus claimed divine authority and rose, then
any visible Church that Christ founded is a teaching authority founded by God.

All four stages are antecedents, which keeps the bridge as weak as possible.
Its content is that Christ's founding act, so vindicated, is God's own act
of founding, and that the authority structure he gave includes teaching. -/
def BridgeChristsChurchFoundedByGod (σ : Signature) : Prop :=
  GodExists σ.IsGod → GodHasClassicalAttributes σ →
    RevelationPossibleAndRecognizable σ → JesusClaimedDivineAuthorityAndRose σ →
    ∀ c, σ.ChristFoundedAsVisibleChurch c → σ.GodFoundedTeachingAuthority c

/-- Every visible Church that Christ founded is a teaching authority founded by
God. An intermediate conclusion of the skeleton. -/
def ChristsChurchIsGodFoundedTeachingAuthority (σ : Signature) : Prop :=
  ∀ c, σ.ChristFoundedAsVisibleChurch c → σ.GodFoundedTeachingAuthority c

/-- Bridge: if God has the classical attributes (among them that he can neither
deceive nor be deceived), then whatever a teaching authority founded by God
definitively proposes as divinely revealed is true. -/
def BridgeGodFoundedAuthorityProposesOnlyTruth (σ : Signature) : Prop :=
  GodHasClassicalAttributes σ →
    ∀ c, σ.GodFoundedTeachingAuthority c →
      ∀ p, σ.DefinitivelyProposesAsRevealed c p → p

/-- The Catholic Church definitively proposes each article of the
Nicene-Constantinopolitan Creed as divinely revealed. A doctrinal-historical
premise, not a consequence of (A). -/
def CatholicChurchDefinitivelyProposesCreed (σ : Signature) : Prop :=
  ∀ p ∈ CreedArticleList σ, σ.DefinitivelyProposesAsRevealed σ.catholicChurch p

end TruthCore.Case.Catholicism
