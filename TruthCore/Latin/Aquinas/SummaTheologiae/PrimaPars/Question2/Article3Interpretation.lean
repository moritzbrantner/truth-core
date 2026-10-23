import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3

/-!
Interpretive vocabulary for the two readings of the *prima via* per se premise
(ST I q.2 a.3 co.).

This module keeps two kinds of statement apart:

* **Formal facts about the readings** (`StrongReadingYieldsUnmovedMover`,
  `WeakReadingDoesNotYieldUnmovedMover`, the objection-scope notions). These are
  propositions about every `MotionModel`; Lean proves or refutes them.
* **Interpretive statements about the text** (what Aquinas wrote, what
  q.46 a.2 ad 7 shows, the charity principle). These stay atomic propositions.
  Lean only checks what follows from them; their truth is source-fidelity work.
-/

namespace TruthCore.Latin.Aquinas.SummaTheologiae

/-- One interpretation of the *prima via* vocabulary: a domain of beings and
respects together with the motion, act and potency, per se link and relevance
predicates. -/
structure MotionModel where
  Being : Type
  Respect : Type
  MovedIn : Being → Respect → Prop
  MovesIn : Being → Being → Respect → Prop
  InPotency : Being → Respect → Prop
  InAct : Being → Respect → Prop
  MovesAsMoved : Being → Being → Prop
  RelevantTo : Being → Being → Respect → Respect → Prop

/-- The premises of the strong reading of the *prima via*, in one model. -/
def StrongPremises (M : MotionModel) : Prop :=
  SomethingIsMovedReading M.MovedIn ∧
  MovedOnlyAsInPotencyReading M.MovedIn M.InPotency ∧
  MovesOnlyAsInActReading M.MovesIn M.InAct ∧
  ReducedOnlyByAMoverReading M.MovedIn M.MovesIn ∧
  NotActAndPotencyInSameRespectReading M.InAct M.InPotency ∧
  SecondMoversMoveOnlyAsMovedReading M.MovedIn M.MovesIn M.MovesAsMoved ∧
  NoInfinitePerSeMoverSeriesReading M.MovesAsMoved

/-- The premises of the weaker (relevant-respect) reading, in one model. -/
def WeakPremises (M : MotionModel) : Prop :=
  SomethingIsMovedReading M.MovedIn ∧
  MovedOnlyAsInPotencyReading M.MovedIn M.InPotency ∧
  MovesOnlyAsInActReading M.MovesIn M.InAct ∧
  ReducedOnlyByAMoverReading M.MovedIn M.MovesIn ∧
  NotActAndPotencyInSameRespectReading M.InAct M.InPotency ∧
  SecondMoversMoveAsMovedInRelevantRespectReading
    M.MovedIn M.MovesIn M.MovesAsMoved M.RelevantTo ∧
  NoInfinitePerSeMoverSeriesReading M.MovesAsMoved

/-- *A nullo movetur*: a first mover moved in no respect cannot be lacking. -/
def AbsoluteConclusion (M : MotionModel) : Prop :=
  FirstUnmovedMoverCannotBeLackingReading M.MovedIn M.MovesIn

/-- A mover unmoved as mover of its series cannot be lacking. -/
def RelativeConclusion (M : MotionModel) : Prop :=
  RelativelyUnmovedMoverCannotBeLackingReading M.MovedIn M.MovesIn M.RelevantTo

/-- Formal fact: on the strong reading the premises yield *a nullo movetur* in
every model. -/
def StrongReadingYieldsUnmovedMover : Prop :=
  ∀ M : MotionModel, StrongPremises M → AbsoluteConclusion M

/-- Formal fact: on the weaker reading the premises do not yield *a nullo
movetur* in every model. -/
def WeakReadingDoesNotYieldUnmovedMover : Prop :=
  ¬ ∀ M : MotionModel, WeakPremises M → AbsoluteConclusion M

/-- Formal fact: the strong per se premise entails the weaker one, so whatever
falsifies the weaker premise also falsifies the strong premise. -/
def StrongPremisesEntailWeakPremises : Prop :=
  ∀ M : MotionModel, StrongPremises M → WeakPremises M

/-- Formal fact: the absolute conclusion entails the relative one, so whatever
falsifies the relative conclusion also falsifies the absolute conclusion. -/
def AbsoluteConclusionEntailsRelative : Prop :=
  ∀ M : MotionModel, AbsoluteConclusion M → RelativeConclusion M

/-- The irrelevant-respect objection, as a situation in a model: some mover is
unmoved in every respect relevant to its moving, yet is moved in some other
respect. On the weaker reading such a mover can be the "first" mover, so the
weaker reading does not reach a mover moved by none. -/
def IrrelevantRespectObjection (M : MotionModel) : Prop :=
  ∃ f x r r', M.MovesIn f x r ∧
    (∀ r'', ¬ (M.MovedIn f r'' ∧ M.RelevantTo f x r r'')) ∧ M.MovedIn f r'

/-- An objection `O` leaves an argument (premises `P`, conclusion `C`) standing
when `O` is jointly satisfiable with the premises, so it falsifies none of them
taken together, and the conclusion still follows wherever the premises and `O`
hold. -/
def LeavesStanding (P C O : MotionModel → Prop) : Prop :=
  (∃ M, P M ∧ O M) ∧ ∀ M, P M → O M → C M

/-- An objection `O` exposes a gap in an argument when some model satisfies the
premises and `O` while the conclusion fails. -/
def ExposesGap (P C O : MotionModel → Prop) : Prop :=
  ∃ M, P M ∧ O M ∧ ¬ C M

/-- Formal fact: the strong premises are jointly satisfiable with the
irrelevant-respect objection. -/
def StrongPremisesCompatibleWithIrrelevantRespectObjection : Prop :=
  ∃ M, StrongPremises M ∧ IrrelevantRespectObjection M

/-- The irrelevant-respect objection leaves the strong-reading *prima via*
standing. -/
def IrrelevantRespectObjectionLeavesStrongStanding : Prop :=
  LeavesStanding StrongPremises AbsoluteConclusion IrrelevantRespectObjection

/-- The irrelevant-respect objection exposes the weaker reading's gap: its
premises do not reach a mover moved by none. -/
def IrrelevantRespectObjectionExposesWeakGap : Prop :=
  ExposesGap WeakPremises AbsoluteConclusion IrrelevantRespectObjection

/-- In q.2 a.3 Aquinas states the conclusion as a first mover moved by none
(*quod a nullo movetur*), without restriction to a respect or to a series.

Source: Thomas Aquinas, *Summa theologiae* I q.2 a.3 co.
-/
def PrimaViaStatesUnrestrictedUnmovedMoverReading (StatesUnrestricted : Prop) :
    Prop :=
  StatesUnrestricted

/-- Aquinas presents that conclusion as following necessarily from the premises
he has just given (*ergo necesse est devenire*).

Source: Thomas Aquinas, *Summa theologiae* I q.2 a.3 co.
-/
def PrimaViaPresentsConclusionAsNecessaryReading (PresentsAsNecessary : Prop) :
    Prop :=
  PresentsAsNecessary

/-- The wording of the dependence premise admits the strong reading: second movers
move only through being moved by the first mover (*non movent nisi per hoc quod
sunt mota a primo movente*), with no restriction to a respect of their being moved.

Source: Thomas Aquinas, *Summa theologiae* I q.2 a.3 co.
-/
def PrimaViaDependenceWordingAdmitsStrongReading (WordingAdmitsStrong : Prop) :
    Prop :=
  WordingAdmitsStrong

/-- Infinite regress is impossible in per se ordered efficient causes (stone,
stick, hand) but not in per accidens series (successive hammers, human
generation), in ST I q.46 a.2 ad 7.

Source: Thomas Aquinas, *Summa theologiae* I q.46 a.2 ad 7.
-/
def InfiniteRegressImpossibleOnlyInPerSeSeriesReading
    (PerSeInfiniteImpossible PerAccidensInfiniteNotImpossible : Prop) : Prop :=
  PerSeInfiniteImpossible ∧ PerAccidensInfiniteNotImpossible

/-- Reading A of q.46 a.2 ad 7: the being-moved it calls accidental to causing is a
completed past generation (*quod sit generatus ab alio*), set against a present
dependence (*si generatio huius hominis dependeret ab hoc homine … et a sole*). So
the passage does not force the weaker reading on the present series of q.2 a.3.

Source: Thomas Aquinas, *Summa theologiae* I q.46 a.2 ad 7.
-/
def Q46DoesNotForceWeakReadingReading (NoTextForcesWeak : Prop) : Prop :=
  NoTextForcesWeak

/-- Reading B of q.46 a.2 ad 7: a cause's being moved counts as accidental whenever
it does not bear on the causing (*generat enim inquantum homo*), whether past or
present. So the passage supports the weaker, relevant-respect reading of the per
se link.

Source: Thomas Aquinas, *Summa theologiae* I q.46 a.2 ad 7.
-/
def Q46SupportsWeakReadingReading (SupportsWeak : Prop) : Prop :=
  SupportsWeak

/-- Interpretive charity principle (project methodology, not a source claim): if
an author states an unrestricted conclusion, presents it as following necessarily,
words a premise so that it admits a reading on which the conclusion follows, the
rival reading does not yield it, and no pinned text forces the rival reading, then
the reading that yields the conclusion is the author's intended one. -/
def ValidityCharityPrinciple
    (StatesUnrestricted PresentsAsNecessary WordingAdmitsStrong NoTextForcesWeak
      StrongIntended : Prop) : Prop :=
  StatesUnrestricted → PresentsAsNecessary → WordingAdmitsStrong →
    StrongReadingYieldsUnmovedMover → WeakReadingDoesNotYieldUnmovedMover →
    NoTextForcesWeak → StrongIntended

/-- The strong per se reading is the one St. Thomas meant in q.2 a.3. -/
def StrongPerSeReadingIntendedReading (StrongIntended : Prop) : Prop :=
  StrongIntended

end TruthCore.Latin.Aquinas.SummaTheologiae
