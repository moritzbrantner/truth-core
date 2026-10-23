/-!
Source-derived readings from Thomas Aquinas, *Summa theologiae* I q.2 a.3 co.,
the *prima via* (argument from motion).

Shared vocabulary, all of it parameters rather than definitions:

* `Being` — the things quantified over. Nothing restricts it to bodies; the
  sensible-motion premise only asserts that *some* being is moved.
* `Respect` — that with respect to which something is moved, e.g. being hot.
  Keeping it abstract leaves open whether *motus* means Aristotelian physical
  motion (place, quality, quantity) or any reduction from potency to act.
* `MovedIn x r` — `x` is being moved (reduced from potency to act) in respect `r`.
* `MovesIn y x r` — `y` moves `x` in respect `r`.
* `InPotency x r`, `InAct x r` — `x` is in potency / in act with respect to `r`.
* `MovesAsMoved y x` — `y` moves `x` only insofar as `y` is itself moved
  (Aquinas' *moventia secunda*, the stick moved by the hand). This is the per se
  (essentially ordered) link of the mover series.

All predicates are read at one and the same time (*simul*). No time index is
formalized; the argument concerns a present series of movers, not a history.

Source witness: SCTA diplomatic TEI of the Leonine edition, vol. 4 (Rome 1888),
`scta-texts/TAca84`, passage `AQUINAS-ST-I-Q2-A3`.
-/

namespace TruthCore.Latin.Aquinas.SummaTheologiae

universe u v

/-- Motion is evident to the senses: something in this world is being moved
(*certum est enim, et sensu constat, aliqua moveri in hoc mundo*).

Only existence is asserted. Whether *moveri* is physical motion or any reduction
from potency to act is left to the abstract `Respect` parameter.

Source: Thomas Aquinas, *Summa theologiae* I q.2 a.3 co.
-/
def SomethingIsMovedReading {Being : Sort u} {Respect : Sort v}
    (MovedIn : Being → Respect → Prop) : Prop :=
  ∃ x r, MovedIn x r

/-- Nothing is moved except insofar as it is in potency to that toward which it is
moved (*nihil enim movetur, nisi secundum quod est in potentia ad illud ad quod
movetur*).

Source: Thomas Aquinas, *Summa theologiae* I q.2 a.3 co.
-/
def MovedOnlyAsInPotencyReading {Being : Sort u} {Respect : Sort v}
    (MovedIn InPotency : Being → Respect → Prop) : Prop :=
  ∀ x r, MovedIn x r → InPotency x r

/-- A thing moves only insofar as it is in act (*movet autem aliquid secundum quod
est actu*), in the same respect in which it moves: fire, actually hot, makes the
wood actually hot.

`InAct` is abstract, so the formal statement does not decide whether the mover
must have the perfection formally (univocal reading) or may have it virtually.
It only requires that the same `InAct` predicate also obey the
non-simultaneity premise.

Source: Thomas Aquinas, *Summa theologiae* I q.2 a.3 co.
-/
def MovesOnlyAsInActReading {Being : Sort u} {Respect : Sort v}
    (MovesIn : Being → Being → Respect → Prop)
    (InAct : Being → Respect → Prop) : Prop :=
  ∀ y x r, MovesIn y x r → InAct y r

/-- Nothing is reduced from potency to act except by something
(*de potentia autem non potest aliquid reduci in actum, nisi per aliquod ens in
actu*); moving just is this reduction (*movere enim nihil aliud est quam educere
aliquid de potentia in actum*).

Only the existence of a mover in the same respect is formalized here. That this
mover is *in act* follows from `MovesOnlyAsInActReading`, so it is not stated twice.

Source: Thomas Aquinas, *Summa theologiae* I q.2 a.3 co.
-/
def ReducedOnlyByAMoverReading {Being : Sort u} {Respect : Sort v}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop) : Prop :=
  ∀ x r, MovedIn x r → ∃ y, MovesIn y x r

/-- Nothing is simultaneously in act and in potency in the same respect, only in
different respects (*non autem est possibile ut idem sit simul in actu et potentia
secundum idem, sed solum secundum diversa*).

Source: Thomas Aquinas, *Summa theologiae* I q.2 a.3 co.
-/
def NotActAndPotencyInSameRespectReading {Being : Sort u} {Respect : Sort v}
    (InAct InPotency : Being → Respect → Prop) : Prop :=
  ∀ x r, ¬ (InAct x r ∧ InPotency x r)

/-- Nothing that is being moved in a respect moves itself in that same respect
(*impossibile est ergo quod, secundum idem et eodem modo, aliquid sit movens et
motum, vel quod moveat seipsum*).

Self-motion in *different* respects (one part moving another) is not excluded.

Source: Thomas Aquinas, *Summa theologiae* I q.2 a.3 co.
-/
def NothingMovesItselfInSameRespectReading {Being : Sort u} {Respect : Sort v}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop) : Prop :=
  ∀ x r, MovedIn x r → ¬ MovesIn x x r

/-- Whatever is moved is moved by another (*omne ergo quod movetur, oportet ab alio
moveri*): by some mover distinct from itself, in the respect in which it is moved.

Source: Thomas Aquinas, *Summa theologiae* I q.2 a.3 co.
-/
def MovedByAnotherReading {Being : Sort u} {Respect : Sort v}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop) : Prop :=
  ∀ x r, MovedIn x r → ∃ y, y ≠ x ∧ MovesIn y x r

/-- Second movers move only insofar as they are moved (*moventia secunda non
movent nisi per hoc quod sunt mota*), as the stick moves only because it is moved
by the hand.

This is the explicit per se ordering premise: when a mover other than the moved
thing is itself being moved, its moving is a per se link `MovesAsMoved` of the
series. Per accidens series (a father who begets, himself begotten) are excluded
from `MovesAsMoved` by this reading, not by the definition of motion.

Source: Thomas Aquinas, *Summa theologiae* I q.2 a.3 co.
-/
def SecondMoversMoveOnlyAsMovedReading {Being : Sort u} {Respect : Sort v}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (MovesAsMoved : Being → Being → Prop) : Prop :=
  ∀ y x r, y ≠ x → MovesIn y x r → (∃ r', MovedIn y r') → MovesAsMoved y x

/-- The per se ordered series of movers cannot proceed to infinity (*hic autem non
est procedere in infinitum*).

Formalized as well-foundedness: every being is accessible under "is moved as a
moved mover by", so no infinite ascending chain of per se moved movers exists.
The premise is restricted to `MovesAsMoved` links; it says nothing about per
accidens series.

Source: Thomas Aquinas, *Summa theologiae* I q.2 a.3 co.
-/
def NoInfinitePerSeMoverSeriesReading {Being : Sort u}
    (MovesAsMoved : Being → Being → Prop) : Prop :=
  ∀ x, Acc MovesAsMoved x

/-- It is necessary to arrive at a first mover moved by none (*ergo necesse est
devenire ad aliquod primum movens, quod a nullo movetur*).

Stated as the reductio Aquinas gives: it is impossible that there be no being
that moves something and is itself moved in no respect. This is classically
equivalent to the plain existential; the double negation keeps the result
axiom-free. The statement does not identify the first mover with God.

Source: Thomas Aquinas, *Summa theologiae* I q.2 a.3 co.
-/
def FirstUnmovedMoverCannotBeLackingReading {Being : Sort u} {Respect : Sort v}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop) : Prop :=
  ¬ ¬ ∃ f, (∃ x r, MovesIn f x r) ∧ ∀ r, ¬ MovedIn f r

/-- What everyone understands by "God" is this first mover moved by none
(*et hoc omnes intelligunt Deum*).

A nominal identification, kept separate from the existence conclusion: every
first mover moved by none falls under what everyone calls God. It attributes no
further divine attribute and is not used by the *prima via* result.

Source: Thomas Aquinas, *Summa theologiae* I q.2 a.3 co.
-/
def FirstUnmovedMoverIsWhatAllUnderstandAsGodReading
    {Being : Sort u} {Respect : Sort v}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (UnderstoodByAllAsGod : Being → Prop) : Prop :=
  ∀ f, ((∃ x r, MovesIn f x r) ∧ ∀ r, ¬ MovedIn f r) → UnderstoodByAllAsGod f

end TruthCore.Latin.Aquinas.SummaTheologiae
