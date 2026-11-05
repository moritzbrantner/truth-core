import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article1

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
`TruthCore.Results.Aquinas.SummaTheologiae.ImmutableIsEternal`).

Source witnesses: SCTA diplomatic TEI of the Leonine edition, passages
`AQUINAS-ST-I-Q9-A1`, `AQUINAS-ST-I-Q10-A1`, `AQUINAS-ST-I-Q18-A3`.
-/

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
*omne autem quod quocumque modo mutatur, est aliquo modo in potentia*), read in
the duration frame: if x's life begins or ends, or has succession, then x is in
potency in some respect.

Reading choices: beginning or ceasing to live and change of life-state count as
being changed *quocumque modo*; "in some way in potency" is read as potency in the
subject, the `InPotency` that `PureAct` quantifies over, not q.9 a.2's power in
another (`STMT-CREATURE-MUTABILITY-THROUGH-CREATOR-POWER`). -/
def ChangeRequiresPotencyReading {Being : Sort u} {Respect : Sort z}
    {Time : Type v} {State : Sort w} [LT Time]
    (InPotency : Being → Respect → Prop)
    (LivesAt : Being → Time → Prop) (lifeStateAt : Being → Time → State) : Prop :=
  ∀ x, (LifeBeginsOrEnds LivesAt x ∨ LifeHasSuccession LivesAt lifeStateAt x) →
    ∃ r, InPotency x r

/-- Open premise, unattributed: whatever is in potency in no respect lives at
some time of the frame. Supported, not stated, by q.18 a.3 co.: what is its own
understanding and has nothing it naturally has determined by another has the
highest degree of life; such is God. The source grounds life in intellect, not in
the bare absence of potency. -/
def PureActLivesReading {Being : Sort u} {Respect : Sort z} {Time : Type v}
    (InPotency : Being → Respect → Prop) (LivesAt : Being → Time → Prop) : Prop :=
  ∀ x, PureAct InPotency x → ∃ t, LivesAt x t

end TruthCore.Latin.Aquinas.SummaTheologiae
