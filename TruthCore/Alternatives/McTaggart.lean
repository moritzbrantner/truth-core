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

end TruthCore.Alternatives.McTaggart
