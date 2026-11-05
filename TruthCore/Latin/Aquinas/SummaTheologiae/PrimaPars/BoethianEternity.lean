module

public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article1

/-!
Typed Boethian eternity for ST I q.10 a.1 (#353).

Aquinas defends Boethius' definition (*Consolatio* V, cited in q.10 a.1 obj. 1):
eternity is *interminabilis vitae tota simul et perfecta possessio*. Its response
gives two marks, both read off from the absence of motion: what is in eternity is
*interminabile*, without beginning and end, and eternity lacks succession,
*tota simul existens*. Reply 2 adds that what is truly eternal is not only a being
but living (*vivens*).

The vocabulary is a duration frame: a type `Time` of times with an earlier-than
relation `<` (no order axiom is assumed or needed), a relation `LivesAt x t`
("x's life is present at t") and the state of that life `lifeStateAt x t`,
which includes its operations (reply 2: duration is measured by operation
rather than bare esse). For something not in time, "present at t" is read as
a.2 ad 4: eternity includes all times. Nothing here identifies `LivesAt` with
biological life or with existence.

* `Interminable`: no two times differ in whether x lives (no beginning or end of
  its life).
* `TotaSimul`: no two times at both of which x lives differ in its life-state (no
  succession).
* `BoethianEternal`: x possesses life at some time, interminably and all at once.

Not encoded: the further connotations of *perfecta* and *possessio* (reply 3:
*nihil ei deest*; reply 6: firm, quiet, indeficient holding). They would need a
perfection/lack vocabulary; reply 6 ties them to immutability itself. The
definition therefore does not reduce to `PureAct`: a non-pure-act being can
satisfy it, and a pure-act being need not (see the controls in
`TruthCore.Results.Aquinas.SummaTheologiae.ImmutableIsBoethianEternal`).

Source witnesses: SCTA diplomatic TEI of the Leonine edition, passages
`AQUINAS-ST-I-Q9-A1`, `AQUINAS-ST-I-Q10-A1`, `AQUINAS-ST-I-Q18-A3`.
-/

@[expose] public section

namespace TruthCore.Latin.Aquinas.SummaTheologiae

universe u v w z

section

variable {Being : Sort u} {Time : Type v} {State : Sort w} [LT Time]

/-- x's life begins or ends: at some earlier and some later time, x lives at one
and not at the other. -/
def LifeBeginsOrEnds (LivesAt : Being → Time → Prop) (x : Being) : Prop :=
  ∃ t₁ t₂, t₁ < t₂ ∧ ¬ (LivesAt x t₁ ↔ LivesAt x t₂)

/-- x's life has succession: x lives at an earlier and a later time and its
life-state differs between them. -/
def LifeHasSuccession (LivesAt : Being → Time → Prop)
    (lifeStateAt : Being → Time → State) (x : Being) : Prop :=
  ∃ t₁ t₂, t₁ < t₂ ∧ LivesAt x t₁ ∧ LivesAt x t₂ ∧ lifeStateAt x t₁ ≠ lifeStateAt x t₂

/-- *Interminabile* (q.10 a.1 co.): x's life has neither beginning nor end. -/
def Interminable (LivesAt : Being → Time → Prop) (x : Being) : Prop :=
  ¬ LifeBeginsOrEnds LivesAt x

/-- *Tota simul* (q.10 a.1 co., ad 5): x's life is without succession. -/
def TotaSimul (LivesAt : Being → Time → Prop)
    (lifeStateAt : Being → Time → State) (x : Being) : Prop :=
  ¬ LifeHasSuccession LivesAt lifeStateAt x

/-- Boethian eternity, *interminabilis vitae tota simul et perfecta possessio*
(q.10 a.1): x possesses life (lives at some time), and that life is interminable
and all at once. -/
def BoethianEternal (LivesAt : Being → Time → Prop)
    (lifeStateAt : Being → Time → State) (x : Being) : Prop :=
  (∃ t, LivesAt x t) ∧ Interminable LivesAt x ∧ TotaSimul LivesAt lifeStateAt x

end

/-- Whatever is changed in any way is in some way in potency (q.9 a.1 co.:
*omne autem quod quocumque modo mutatur, est aliquo modo in potentia*), read only
for succession in the duration frame: if a living thing's life-state differs
between two times at which it lives, it is in potency in some respect.

Reading choices: change of life-state while living is a change *quocumque modo*;
"in some way in potency" is read as potency in the subject, the `InPotency` that
`PureAct` quantifies over, not q.9 a.2's power in another
(`DISAMB-POTENCY-IN-SUBJECT-VS-IN-ANOTHER`). Beginning or ceasing to live is not
covered: Aquinas denies that creation is a change properly speaking, so that
coverage is the separate open premise `LifeBoundaryRequiresPotencyReading`. -/
def SuccessionRequiresPotencyReading {Being : Sort u} {Respect : Sort z}
    {Time : Type v} {State : Sort w} [LT Time]
    (InPotency : Being → Respect → Prop)
    (LivesAt : Being → Time → Prop) (lifeStateAt : Being → Time → State) : Prop :=
  ∀ x, LifeHasSuccession LivesAt lifeStateAt x → ∃ r, InPotency x r

/-- Open premise, unattributed: whatever begins or ceases to live (between an
earlier and a later time of the frame) is in potency in itself in some respect.
Supported, not stated, by q.10 a.1 co.: what is altogether immutable can have
neither beginning nor end. That sentence gives only that what has a beginning or
end is not altogether immutable, which q.9 a.2 allows to hold through a power in
another; the step to potency in the subject is the added commitment. -/
def LifeBoundaryRequiresPotencyReading {Being : Sort u} {Respect : Sort z}
    {Time : Type v} [LT Time]
    (InPotency : Being → Respect → Prop) (LivesAt : Being → Time → Prop) : Prop :=
  ∀ x, LifeBeginsOrEnds LivesAt x → ∃ r, InPotency x r

/-- Open premise, unattributed: whatever is in potency in no respect lives at
some time of the frame. Supported, not stated, by q.18 a.3 co.: what is its own
understanding and has nothing it naturally has determined by another has the
highest degree of life; such is God. The source grounds life in intellect, not in
the bare absence of potency. -/
def PureActLivesReading {Being : Sort u} {Respect : Sort z} {Time : Type v}
    (InPotency : Being → Respect → Prop) (LivesAt : Being → Time → Prop) : Prop :=
  ∀ x, PureAct InPotency x → ∃ t, LivesAt x t

/-- The typed specialization of `ImmutableIsEternalReading`: whatever is in
potency in no respect is Boethian-eternal. It is a distinct statement from the
primitive-`Eternal` reading the root routes consume; identifying the two needs a
recognition commitment that primitive eternity is (or follows from) Boethian
eternity, which is not asserted here. -/
def ImmutableIsBoethianEternalReading {Being : Sort u} {Respect : Sort z}
    {Time : Type v} {State : Sort w} [LT Time]
    (InPotency : Being → Respect → Prop)
    (LivesAt : Being → Time → Prop) (lifeStateAt : Being → Time → State) : Prop :=
  ∀ x, PureAct InPotency x → BoethianEternal LivesAt lifeStateAt x

end TruthCore.Latin.Aquinas.SummaTheologiae
