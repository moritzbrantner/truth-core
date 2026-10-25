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

Only theories and consistency claims live in this namespace: `bind-check`
treats every `TruthCore.Comparison.*` definition as a theory bundle.

A theory is a predicate on interpretations `s : Sig` of the shared vocabulary.
It enters results only as a hypothesis or, for consistency, through an explicit
interpretation that satisfies it. Nothing here is an axiom.

The signature reuses the *prima via* vocabulary of #151 (`MotionModel`: beings,
respects, being moved, moving, potency, act, per se ordering). God is what all
understand by that name, which #151 identifies with the first mover moved by
none. Goods are perfections a being has in act (I q.5 a.1).

Question `Q-MORAL-GROUNDING`: what makes something objectively good or evil?

* O'Connor's emotivism: nothing does. Moral statements have no truth value
  (`MoralStatementsLackTruthValueReading`; its cell is
  `POE-EXTERNAL-PREMISE-VS-EMOTIVISM`, over the man-made-evil premise).
* The Catholic theory: goodness is the same in reality as being in act; evil is
  the privation of a due good; "there is evil" is true when such a privation
  is in a subject (`CatholicGrounding`).
* Naturalist moral realism: primary Railton and Boyd witnesses and scoped
  comparison bundles are now recorded in `Comparison.NaturalisticRealism`
  (#249; see `docs/naturalistic-moral-realism.md`). This problem-of-evil
  signature has not been expanded with their distinct normative vocabulary.
-/

namespace TruthCore.Comparison.ProblemOfEvil

open TruthCore.English.OConnor
open TruthCore.Latin.Aquinas.SummaTheologiae


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
  Holds : Sentence → Prop
  /-- The sentence "there is evil in the world". -/
  evilPremise : Sentence

/-- Shared background for the internal form: an all-powerful being can
eliminate any evil (O'Connor, 2020). It is a one-conjunct bundle so that it can
grow without changing the results' shape. -/
def Background (s : Sig) : Prop :=
  AllPowerfulCanEliminateEvilReading s.Omnipotent s.Evil s.CanEliminate

/-- There is evil in some being (ST I q.48 a.2). -/
def EvilExists (s : Sig) : Prop :=
  EvilIsFoundInThingsReading s.Evil

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

/-- The internal form fails: the background, the Catholic theory and the
existence of evil are jointly satisfiable. -/
def CatholicTheoryConsistentWithEvil : Prop :=
  ∃ s : Sig, Background s ∧ Catholic s ∧ EvilExists s

end TruthCore.Comparison.ProblemOfEvil
