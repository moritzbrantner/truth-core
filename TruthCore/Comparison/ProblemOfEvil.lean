import TruthCore.English.OConnor.Metaethics
import TruthCore.English.OConnor.ProblemOfEvil
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3Interpretation
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3Evil
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question5.Article1
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question48.Articles2and3

/-!
The problem-of-evil comparison (#150): a shared signature, the shared
background, and the theories as sets of source readings (owner decision on
#149: for now a theory is a set of propositions and arguments).

A theory is a predicate on interpretations `s : Sig` of the shared vocabulary.
It enters results only as a hypothesis or, for consistency, through an explicit
interpretation that satisfies it. Nothing here is an axiom.

The signature reuses the *prima via* vocabulary of #151 (`MotionModel`: beings,
respects, being moved, moving, potency, act, per se ordering). God is what all
understand by that name, which #151 identifies with the first mover moved by
none. Goods are perfections a being has in act (I q.5 a.1).

Question `Q-MORAL-GROUNDING`: what makes something objectively good or evil?

* O'Connor's emotivism: nothing does. Moral statements have no truth value
  (`Emotivism`).
* The Catholic theory: goodness is the same in reality as being in act; evil is
  the privation of a due good; "there is evil" is true when such a privation
  is in a subject (`CatholicGrounding`).
* Naturalist moral realism: no pinned proponent yet; recorded as a candidate,
  so it has no definition here.
-/

namespace TruthCore.Comparison.ProblemOfEvil

open TruthCore.English.OConnor
open TruthCore.Latin.Aquinas.SummaTheologiae

universe u

/-- The shared signature of the problem-of-evil question set. -/
structure Sig where
  /-- Beings, respects, and the motion vocabulary of the *prima via* (#151). -/
  motion : MotionModel
  Perfection : Type
  Sentence : Type
  /-- `x` actually has perfection `p`. -/
  Has : motion.Being → Perfection → Prop
  /-- `p` is a good due to `x`. -/
  Due : motion.Being → Perfection → Prop
  /-- `x` is good in respect of `p`. -/
  GoodIn : motion.Being → Perfection → Prop
  /-- There is evil in `x`. -/
  Evil : motion.Being → Prop
  /-- `g` falls under what all understand by "God". -/
  God : motion.Being → Prop
  SupremelyGood : motion.Being → Prop
  Omnipotent : motion.Being → Prop
  /-- `g` is able to eliminate the evil in `x`. -/
  CanEliminate : motion.Being → motion.Being → Prop
  /-- `g` brings the good of `p` in `y` out of the evil in `x`. -/
  DrawsGoodFrom : motion.Being → motion.Being → motion.Being → Perfection → Prop
  /-- `φ` says of something that it is bad. -/
  SaysSomethingBad : Sentence → Prop
  Moral : Sentence → Prop
  TruthApt : Sentence → Prop
  Holds : Sentence → Prop
  /-- The sentence "there is evil in the world". -/
  evilPremise : Sentence

/-- Shared background: saying that something is bad is a moral statement
(O'Connor, 2023); the evil premise says that something is bad (ST I q.2 a.3
obj. 1); an all-powerful being can eliminate any evil (O'Connor, 2020). -/
def Background (s : Sig) : Prop :=
  BadnessAscriptionsAreMoralReading s.SaysSomethingBad s.Moral ∧
    EvilPremiseSaysSomethingBadReading s.SaysSomethingBad s.evilPremise ∧
    AllPowerfulCanEliminateEvilReading s.Omnipotent s.Evil s.CanEliminate

/-- The external form's premise: "there is evil in the world" is true
(ST I q.2 a.3 obj. 1). -/
def ExternalEvilPremise (s : Sig) : Prop :=
  EvilPremiseAssertedReading s.Holds s.evilPremise

/-- There is evil in some being (ST I q.48 a.2). -/
def EvilExists (s : Sig) : Prop :=
  EvilIsFoundInThingsReading s.Evil

/-- O'Connor's answer to `Q-MORAL-GROUNDING` (2023): moral statements have no
truth value, and what has no truth value is not true. -/
def Emotivism (s : Sig) : Prop :=
  MoralStatementsLackTruthValueReading s.Moral s.TruthApt ∧
    LackingTruthValueExcludesTruthReading s.TruthApt s.Holds

/-- The Catholic answer to `Q-MORAL-GROUNDING` (ST I q.5 a.1; q.48 a.2 ad 2,
a.3). -/
def CatholicGrounding (s : Sig) : Prop :=
  GoodnessIsActualityReading s.GoodIn s.Has ∧
    EvilIsPrivationReading s.Evil s.Due s.Has ∧
    EvilIsAsPropositionalTruthReading s.Evil s.Holds s.evilPremise

/-- The Catholic theory's commitments in this question set, as one flat
conjunction so that `bind-check` binds each to its statement:

1. its grounding answer (the three conjuncts of `CatholicGrounding`);
2. some things fall short of their due good (ST I q.48 a.2);
3. the seven premises of the strong-reading *prima via* (ST I q.2 a.3, #151);
4. what all understand as God is the first mover moved by none (#151);
5. God is supremely good and omnipotent (q.2 a.3 ad 1);
6. God brings good out of every evil (q.2 a.3 ad 1), the reason for permission.
-/
def Catholic (s : Sig) : Prop :=
  GoodnessIsActualityReading s.GoodIn s.Has ∧
    EvilIsPrivationReading s.Evil s.Due s.Has ∧
    EvilIsAsPropositionalTruthReading s.Evil s.Holds s.evilPremise ∧
    SomethingFallsShortOfDueGoodReading s.Due s.Has ∧
    SomethingIsMovedReading s.motion.MovedIn ∧
    MovedOnlyAsInPotencyReading s.motion.MovedIn s.motion.InPotency ∧
    MovesOnlyAsInActReading s.motion.MovesIn s.motion.InAct ∧
    ReducedOnlyByAMoverReading s.motion.MovedIn s.motion.MovesIn ∧
    NotActAndPotencyInSameRespectReading s.motion.InAct s.motion.InPotency ∧
    SecondMoversMoveOnlyAsMovedReading s.motion.MovedIn s.motion.MovesIn s.motion.MovesAsMoved ∧
    NoInfinitePerSeMoverSeriesReading s.motion.MovesAsMoved ∧
    FirstUnmovedMoverIsWhatAllUnderstandAsGodReading s.motion.MovedIn s.motion.MovesIn s.God ∧
    GodSupremelyGoodAndOmnipotentReading s.God s.SupremelyGood s.Omnipotent ∧
    GodDrawsGoodFromEveryEvilReading s.God s.Evil s.GoodIn s.DrawsGoodFrom

/-- The evil premise is not true. With the external premise that it is
(ST I q.2 a.3 obj. 1), this yields `False`. -/
def EvilPremiseNotTrue {Sentence : Sort u} (Holds : Sentence → Prop) (evilPremise : Sentence) :
    Prop :=
  ¬ Holds evilPremise

/-- The internal form fails: the background, the Catholic theory and the
existence of evil are jointly satisfiable. -/
def CatholicTheoryConsistentWithEvil : Prop :=
  ∃ s : Sig, Background s ∧ Catholic s ∧ EvilExists s

/-- The first objection's conditional (if God exists, there is no evil) fails
at `s`. -/
def ObjectionOneFails (s : Sig) : Prop :=
  ¬ GodWouldExcludeAllEvilObjectionReading s.God s.Evil

end TruthCore.Comparison.ProblemOfEvil
