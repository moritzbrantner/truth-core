import TruthCore.Alternatives.ActPotencyRegress

/-!
McTaggart's own commitment about change, and the weak bridge from the prima
via's motion to it (#497).

New vocabulary, a parameter: `Changes x`, McTaggart's general "change": `x`
changes in some characteristic, quality or relation ("A universe in which
nothing whatever changed (including the thoughts of the conscious beings in it)
would be a timeless universe"). It is neither A-series change (`ASeriesChanges`,
`DEF-A-SERIES-CHANGE`) nor reduction from potency to act (`MovedIn`,
`DEF-MOTION-AS-REDUCTION`); `DISAMB-CHANGE-A-SERIES` keeps the three apart.
-/

namespace TruthCore.Alternatives.McTaggart

universe u v

/-- McTaggart: all change is change of A-series determinations ("we seem
forced to the conclusion that all change is only a change of the
characteristics imparted to events by their presence in the A series";
"Without the A series then, there would be no change"). Read as: if anything
changes, some event changes in its A-series determinations.

Weakest reading: it does not say that the changing thing is itself the event
whose A-determinations change, nor anything about `MovedIn`.

Source: J. M. E. McTaggart, "The Unreality of Time", *Mind* 17 (1908).
-/
def AllChangeIsASeriesChangeReading {Being : Sort u}
    (Changes ASeriesChanges : Being → Prop) : Prop :=
  ∀ x, Changes x → ∃ e, ASeriesChanges e

/-- Open bridge, unattributed: whatever is being moved in some respect (reduced
from potency to act) changes, in McTaggart's general sense of change.

It is weaker than `BeingMovedInvolvesASeriesChangeReading`: it says nothing
about the A series, so a B-theorist who keeps change as variation along the B
series accepts it. Aristotle's "every motion is a change" (*Physics* V.1,
ἐπεὶ δὲ πᾶσα κίνησις μεταβολή τις) motivates it, but identifying μεταβολή
with McTaggart's "change" is a reading step no source states, so no claim
attributes it. -/
def MotionIsChangeReading {Being : Sort u} {Respect : Sort v}
    (MovedIn : Being → Respect → Prop) (Changes : Being → Prop) : Prop :=
  ∀ x r, MovedIn x r → Changes x

/-- McTaggart's answer to the retorsion (*The Nature of Existence* II, 1927):
there are appearings (perceptions, some of which appear as judgments, of
things as in time), and no appearer, as such, changes.

He grants that the appearance is "beyond doubt" (§ 506) and that "a
misperception is ... as real as a correct perception" (§ 517); everything,
myself included, is perceived as in time, "while in reality none of them are
in time" (§ 516); and the denial of time is not self-refuting, because "my
denial that Z is really in time does not involve that Y, that denial, is
really in time" (§ 511, contrasted with the vicious regress in denying
error, § 510). With "where there is time, there is change" and a non-temporal
series "allows of no change" (ch. XXXIII, § 316), the appearer does not change.

Weakest reading: it says only that opiners do not change in the general
sense (`DEF-CHANGE-GENERAL`); it says nothing about `MovedIn` (reduction from
potency to act), and nothing about the C series, the real non-temporal order
that McTaggart says appears as time (§ 347, ch. XLV). `Opines` is read
tenselessly here: for McTaggart an appearer opines at a C-series position, not
"now". -/
def AppearingsDoNotChangeReading {Being : Sort u}
    (Opines : Being → Prop → Prop) (Changes : Being → Prop) : Prop :=
  (∃ x p, Opines x p) ∧ ∀ x p, Opines x p → ¬ Changes x

open TruthCore.Alternatives.ActPotencyRegress in
/-- McTaggart's answer and the open bridge `MotionIsChangeReading` together
deny `OpiningIsBeingMovedReading`. So he is a sourced proponent of the denial
of `STMT-OPINION-IS-A-MOTION`, given only that bridge; the retorsion against
him assumes what he denies. -/
theorem appearingsDoNotChange_denies_opinionIsMotion {Being : Sort u} {Respect : Sort v}
    {MovedIn : Being → Respect → Prop} {Opines : Being → Prop → Prop}
    {Changes : Being → Prop} {asOpinion : Prop → Respect}
    (hReply : AppearingsDoNotChangeReading Opines Changes)
    (hBridge : MotionIsChangeReading MovedIn Changes) :
    ¬ OpiningIsBeingMovedReading MovedIn Opines asOpinion :=
  fun h =>
    let ⟨⟨x, p, hx⟩, hNo⟩ := hReply
    hNo x p hx (hBridge x _ (h x p hx))

end TruthCore.Alternatives.McTaggart
