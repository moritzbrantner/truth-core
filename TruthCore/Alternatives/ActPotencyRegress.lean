import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3SecundaVia
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question4.Article1

/-!
Rivals of the act/potency and causal-regress premises on the root path (#387),
and the premises of the three refutations proved in
`TruthCore.Results.Alternatives`.

Every rival is stated in the *prima via* and *secunda via* vocabulary
(`Being`, `Respect`, `MovedIn`, `MovesIn`, `InAct`, `InPotency`,
`MovesAsMoved`, `CausesAsCaused`, `EfficientlyCausesIn`, `PriorSimply`; see
`TruthCore.Latin.Aquinas.SummaTheologiae`), so that each rival can be compared
with the premise it rivals directly. New vocabulary, all of it parameters:

* `Opines x p` — `x` is opining (judging, having it appear) that `p`.
* `asOpinion p` — the respect in which an opiner of `p` is affected by opining
  it. Whether this is a respect in which the opiner is *moved* is exactly the
  premise `OpiningIsBeingMovedReading`; nothing here decides it.
* `CanBe x r` — `x` is able to be `r`, the primitive of the *Metaphysics* Θ.6
  analysis (`TruthCore.Greek.Aristotle.Metaphysics.PotencyIsUnactualizedCapacityReading`,
  `DEF-CAPACITY-TO-BE`).
* `UniformLocalMotion r` — `r` is a respect of uniform rectilinear local motion
  (Newton's *status movendi uniformiter in directum*).

A rival is recorded as a statement in its own right (invariant 6), never as the
bare negation of the premise it rivals, and each definition says how it clashes
with that premise. Refutations are in separate result modules.
-/

namespace TruthCore.Alternatives.ActPotencyRegress

open TruthCore.Latin.Aquinas.SummaTheologiae

universe u v

/-! ## Rivals -/

/-- Eleatic rival to `SomethingIsMovedReading`: nothing is being moved in any
respect. Aristotle reports it as the view that being is infinite and unmoved
(*Physics* VIII.3, 254a24-25, εἶναι τὸ ὂν ἄπειρον καὶ ἀκίνητον, ascribed to
"some"; the formula is Melissus').

Only the present-tense content is formalized, in the shared `MovedIn`
vocabulary; the Eleatic arguments for it (Zeno) are not.

Source: Aristotle, *Physics* VIII.3, 253a32-b2, 254a23-25.
-/
def NothingIsMovedReading {Being : Sort u} {Respect : Sort v}
    (MovedIn : Being → Respect → Prop) : Prop :=
  ∀ x r, ¬ MovedIn x r

/-- McTaggart's rival to `SomethingIsMovedReading`: nothing really changes,
though there are appearances of change. "Whenever we judge anything to exist in
time, we are in error. And whenever we perceive anything as existing in time ...
we are perceiving it more or less as it really is not."

It differs from the bare Eleatic thesis by granting that judgings and
perceivings occur: the second conjunct. With `OpiningIsBeingMovedReading` it is
inconsistent; McTaggart denies that premise for appearances (he raises the
question whether an appearance of change must itself change and promises an
answer, last paragraph of the paper).

Source: J. M. E. McTaggart, "The Unreality of Time", *Mind* 17 (1908).
-/
def ChangeUnrealButAppearsReading {Being : Sort u} {Respect : Sort v}
    (MovedIn : Being → Respect → Prop) (Opines : Being → Prop → Prop) : Prop :=
  NothingIsMovedReading MovedIn ∧ ∃ x p, Opines x p

/-- Rival to `NotActAndPotencyInSameRespectReading`: something is in act and in
potency in the same respect. Duns Scotus' defence of self-motion (a thing can
be *virtually* in act and *formally* in potency with respect to the same
perfection, so that it moves itself) is its motivating instance; on the shared
`InAct` predicate, which `MovesOnlyAsInActReading` needs to cover virtual act
(`DISAMB-IN-ACT`), the self-mover is a witness of this statement.

Waiting for a witness (Scotus, *Quaestiones super libros Metaphysicorum* IX
q.14); no claim attributes it yet.
-/
def InActAndPotencyInSameRespectReading {Being : Sort u} {Respect : Sort v}
    (InAct InPotency : Being → Respect → Prop) : Prop :=
  ∃ x r, InAct x r ∧ InPotency x r

/-- Rival to `ActualityOnlyInsofarAsBeingReading`: something is in act in some
respect without having being. Meinong's principle of the independence of
*Sosein* from *Sein* (the golden mountain is golden but is not) is its
motivating instance.

Waiting for a witness (Meinong, "Über Gegenstandstheorie", 1904, §3); no claim
attributes it yet.
-/
def ActualityWithoutBeingReading {Being : Sort u} {Respect : Sort v}
    (InAct : Being → Respect → Prop) (esse : Respect) : Prop :=
  ∃ x r, InAct x r ∧ ¬ InAct x esse

/-- Rival to `ActSimplyPriorToPotencyReading`: some potency is not simply
posterior to any being in act in that respect, i.e. potency is prior. Aristotle
states it as the reputable view (δοκεῖ) that "everything that acts is able, but
not everything able acts, so that potency is prior", and ascribes the same
consequence to the theologians who generate the world from Night and the
physicists' "all things together".

Source: Aristotle, *Metaphysics* XII.6, 1071b22-28.
-/
def PotencyPriorToActReading {Being : Sort u} {Respect : Sort v}
    (InAct InPotency : Being → Respect → Prop)
    (PriorSimply : Being → Being → Prop) : Prop :=
  ∃ x r, InPotency x r ∧ ∀ y, InAct y r → ¬ PriorSimply y x

/-- Rival to `MovesOnlyAsInActReading`: something moves another in a respect
without being in act in that respect, as on emergentist accounts lower-level
causes produce a quality none of them has.

On the virtual reading of `InAct` (`DISAMB-IN-ACT`) an emergent cause is in act
virtually and the statement does not hold of it; it bites only on the formal
reading. Waiting for a witness (C. D. Broad, *The Mind and Its Place in
Nature*, 1925, ch. 2; copyrighted, #378).
-/
def MovesWithoutBeingInActReading {Being : Sort u} {Respect : Sort v}
    (MovesIn : Being → Being → Respect → Prop)
    (InAct : Being → Respect → Prop) : Prop :=
  ∃ y x r, MovesIn y x r ∧ ¬ InAct y r

/-- Newtonian rival to `ReducedOnlyByAMoverReading`: some body is being moved
in a respect of uniform rectilinear motion and nothing moves it in that
respect. Newton's first law: every body perseveres in its state of rest or of
uniform motion in a straight line except insofar as impressed forces compel it
to change that state.

Reading choice: Newton does not say that uniform motion is a *being moved*
(`MovedIn`, a reduction from potency to act). The statement reads it so and
reads "impressed force" as the only candidate mover; the Thomist reply denies
the first reading (`DISAMB-MOTION`).

Source: Newton, *Philosophiae naturalis principia mathematica* (1687),
Axiomata sive leges motus, Lex I.
-/
def UniformMotionWithoutMoverReading {Being : Sort u} {Respect : Sort v}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (UniformLocalMotion : Respect → Prop) : Prop :=
  ∃ x r, UniformLocalMotion r ∧ MovedIn x r ∧ ∀ y, ¬ MovesIn y x r

/-- Indeterminist rival to `ReducedOnlyByAMoverReading`: some change happens
with nothing moving the changing thing in that respect, as on the standard
reading of quantum mechanics a radioactive nucleus decays at no determined
time and with no determining cause.

The statement is about any respect, not only local motion, so it is a different
proposition from `UniformMotionWithoutMoverReading`. Waiting for a witness
(Born 1926; copyrighted, #378).
-/
def ChangeWithoutAnyMoverReading {Being : Sort u} {Respect : Sort v}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop) : Prop :=
  ∃ x r, MovedIn x r ∧ ∀ y, ¬ MovesIn y x r

/-- The Megarian thesis: a thing is able only when it is acting (ὅταν ἐνεργῇ
μόνον δύνασθαι), as the one not building is not able to build. Stated with the
Θ.6 primitive `CanBe`: whatever is able to be `r` is actually `r`.

It rivals `MovedOnlyAsInPotencyReading` through the Θ.6 analysis
(`PotencyIsUnactualizedCapacityReading`: in potency = able and not actual):
with that analysis it leaves nothing in potency, so whatever is moved is moved
without being in potency. Aristotle's reply is that it abolishes motion and
becoming (1047a10-17), proved, given open premises, in result
`MEGARIAN-THESIS-ABOLISHES-MOTION`.

Source: Aristotle, *Metaphysics* IX.3, 1046b29-32.
-/
def MegarianAbilityOnlyWhenActingReading {Being : Sort u} {Respect : Sort v}
    (InAct CanBe : Being → Respect → Prop) : Prop :=
  ∀ x r, CanBe x r → InAct x r

/-- Ash'arite occasionalist rival to `MovedOnlyAsInPotencyReading`: things are
moved (pass to new states) without being in potency to them, because each state
is created anew by God and a creature's capacity exists only together with its
act, never before it.

Waiting for a witness (al-Ghazali, *Tahafut al-falasifa*, discussion 17;
al-Ash'ari). Whether re-creation is a *being moved* in the sense of
`DEF-MOTION-AS-REDUCTION` is the open reading question (`DISAMB-MOTION`).
-/
def MovedWithoutPotencyReading {Being : Sort u} {Respect : Sort v}
    (MovedIn InPotency : Being → Respect → Prop) : Prop :=
  ∃ x r, MovedIn x r ∧ ¬ InPotency x r

/-- Rival to `SecondMoversMoveOnlyAsMovedReading`: some mover other than the
moved thing is itself being moved in some respect, and yet does not move it as
moved (its moving is no per se link), as a man digesting while he moves a
stick. Aquinas' own example of an accidental cause (the father generates as
man, not as son, ST I q.46 a.2 ad 7) is the reason for the weaker sibling
reading `SecondMoversMoveAsMovedInRelevantRespectReading`.
-/
def MovedMoverMovesNotAsMovedReading {Being : Sort u} {Respect : Sort v}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (MovesAsMoved : Being → Being → Prop) : Prop :=
  ∃ y x r r', y ≠ x ∧ MovesIn y x r ∧ MovedIn y r' ∧ ¬ MovesAsMoved y x

/-- Rival to `NoInfinitePerSeEfficientCauseSeriesReading`: there is an
infinite descending per se series of efficient causes, each a middle cause of
the one before, with no first. The countermodels `INFINITE-LOCAL-TRANSMISSION-MODEL`
and `ESSENTIAL-POWER-UNDERDETERMINED` show that such a series is consistent
with local transmission rules (#310).

Waiting for a witness (infinitism about ground, copyrighted, #378).
-/
def InfinitePerSeCauseSeriesReading {Being : Sort u}
    (CausesAsCaused : Being → Being → Prop) : Prop :=
  ∃ f : Nat → Being, ∀ n, CausesAsCaused (f (n + 1)) (f n)

/-- Rival to `NoInfinitePerSeEfficientCauseSeriesReading`: some being is,
through a finite chain of per se links, a middle cause of itself (a per se
causal loop; the bootstrap structures of #311). Well-foundedness excludes it,
since a being on a cycle is not accessible.

Waiting for a witness (coherentism about ground; copyrighted, #378). Refuted,
given open premises, from the Second Way's own priority premises in result
`PER-SE-CAUSAL-LOOP-IMPOSSIBLE`.
-/
def PerSeCausalLoopReading {Being : Sort u}
    (CausesAsCaused : Being → Being → Prop) : Prop :=
  ∃ x, Relation.TransGen CausesAsCaused x x

/-- Occasionalist rival to `PerSeMoverLinkIsPerSeCauseLinkReading`: some per
se link of a mover series is no per se link of efficient causes, because the
moved mover (the stick) is only the occasion on which God causes the motion and
is no efficient cause at all.

Waiting for a witness (Malebranche, *De la recherche de la vérité* VI.ii.3;
al-Ghazali, *Tahafut*, discussion 17).
-/
def MoverLinkWithoutCauseLinkReading {Being : Sort u}
    (MovesAsMoved CausesAsCaused : Being → Being → Prop) : Prop :=
  ∃ y x, MovesAsMoved y x ∧ ¬ CausesAsCaused y x

/-! ## Premises of the refutations -/

/-- Opinion and imagination are motions (ἡ γὰρ φαντασία καὶ ἡ δόξα κινήσεις
τινὲς εἶναι δοκοῦσιν): whoever opines that `p` is thereby being moved in the
respect of that opinion.

Aristotle hedges (δοκοῦσιν, "are thought to be"); the premise records the
reputable opinion he relies on, not a demonstration.

Source: Aristotle, *Physics* VIII.3, 254a27-30.
-/
def OpiningIsBeingMovedReading {Being : Sort u} {Respect : Sort v}
    (MovedIn : Being → Respect → Prop) (Opines : Being → Prop → Prop)
    (asOpinion : Prop → Respect) : Prop :=
  ∀ x p, Opines x p → MovedIn x (asOpinion p)

/-- The Eleatic thesis is held: someone opines that nothing is moved (καθάπερ
φασί τινες, εἶναι τὸ ὂν ἄπειρον καὶ ἀκίνητον).

This is the self-applicative premise: a rival that is held by no one is no
rival (#387), so the premise holds of any recorded Eleatic.

Source: Aristotle, *Physics* VIII.3, 254a24-25.
-/
def EleaticThesisIsOpinedReading {Being : Sort u} {Respect : Sort v}
    (MovedIn : Being → Respect → Prop) (Opines : Being → Prop → Prop) : Prop :=
  ∃ x, Opines x (NothingIsMovedReading MovedIn)

/-- Conclusion of the retorsion: the Eleatic thesis is false. -/
def EleaticThesisFalse {Being : Sort u} {Respect : Sort v}
    (MovedIn : Being → Respect → Prop) : Prop :=
  ¬ NothingIsMovedReading MovedIn

/-- What is being moved toward `r` is not yet actually `r`: motion is an
actuality, but incomplete, because the potential whose actuality it is is
incomplete (ἡ τε κίνησις ἐνέργεια μὲν εἶναί τις δοκεῖ, ἀτελὴς δέ).

Reading choice: "incomplete" is read as "not yet having the perfection toward
which the motion goes". It does not say that the moved thing is in act in no
respect.

Source: Aristotle, *Physics* III.2, 201b31-33.
-/
def MovedNotYetInActReading {Being : Sort u} {Respect : Sort v}
    (MovedIn InAct : Being → Respect → Prop) : Prop :=
  ∀ x r, MovedIn x r → ¬ InAct x r

/-- What is coming to be `r` is able to be `r`: what is unable to come to be
will not come to be, and whoever says that what is unable to come to be is or
will be speaks falsely, "for this is what 'unable' meant" (τὸ γὰρ ἀδύνατον
τοῦτο ἐσήμαινεν).

Read with `MovedIn x r` as `x`'s coming to be `r`: whatever is being moved
toward `r` is able to be `r`.

Source: Aristotle, *Metaphysics* IX.3, 1047a11-14.
-/
def MovedIsAbleToBeReading {Being : Sort u} {Respect : Sort v}
    (MovedIn CanBe : Being → Respect → Prop) : Prop :=
  ∀ x r, MovedIn x r → CanBe x r

/-- Conclusion of Aristotle's reply: the Megarian thesis is false. -/
def MegarianThesisFalse {Being : Sort u} {Respect : Sort v}
    (InAct CanBe : Being → Respect → Prop) : Prop :=
  ¬ MegarianAbilityOnlyWhenActingReading InAct CanBe

/-- A middle cause efficiently causes what it is the middle cause of (*medium
est causa ultimi*): whatever causes `x` as caused efficiently causes `x` in some
respect.

Source: Thomas Aquinas, *Summa theologiae* I q.2 a.3 co., second way.
-/
def MiddleCauseEfficientlyCausesReading {Being : Sort u} {Respect : Sort v}
    (EfficientlyCausesIn : Being → Being → Respect → Prop)
    (CausesAsCaused : Being → Being → Prop) : Prop :=
  ∀ c x, CausesAsCaused c x → ∃ r, EfficientlyCausesIn c x r

/-- Simple priority is transitive: what is prior to something prior to `x` is
prior to `x`.

Open and not yet sourced. The Second Way's "the first is the cause of the
middle and the middle of the last ... remove the cause and the effect is
removed" is the natural witness, but it speaks of causes, not of simple
priority.
-/
def SimplePriorityTransitiveReading {Being : Sort u}
    (PriorSimply : Being → Being → Prop) : Prop :=
  ∀ x y z, PriorSimply x y → PriorSimply y z → PriorSimply x z

/-- Conclusion: there is no per se causal loop. -/
def NoPerSeCausalLoop {Being : Sort u}
    (CausesAsCaused : Being → Being → Prop) : Prop :=
  ¬ PerSeCausalLoopReading CausesAsCaused

end TruthCore.Alternatives.ActPotencyRegress
