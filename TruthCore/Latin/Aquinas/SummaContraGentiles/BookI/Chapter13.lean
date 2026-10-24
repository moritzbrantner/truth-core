/-!
Source-derived reading from Thomas Aquinas, *Summa contra Gentiles* I.13
[29]-[30], used by the eternal-world dilemma for the *tertia via* (owner
decision on #143, 2026-10-24).

Vocabulary as in the *tertia via* (`IsAt x t`: `x` is at time `t`;
`Before t t'`: `t` is earlier than `t'`), plus `CausesOrigin c x`: `c` is the
cause from which `x`'s coming to be takes its origin.

Source witness: the English translation of A. C. Pegis (web snapshot, passage
`AQUINAS-SCG-I-13-EN`); claims on it carry `basis: translation`.
-/

namespace TruthCore.Latin.Aquinas.SummaContraGentiles

universe u v

/-- `x` comes to be anew: either it is not at one time and is at a later one, or
it is at a time before which there is no time (it begins with time itself). -/
def ComesToBeAnew {Being : Sort u} {Time : Sort v}
    (IsAt : Being → Time → Prop) (Before : Time → Time → Prop) (x : Being) : Prop :=
  (∃ t1 t2, Before t1 t2 ∧ ¬ IsAt x t1 ∧ IsAt x t2) ∨
    (∃ t, IsAt x t ∧ ∀ t', ¬ Before t' t)

/-- What comes to be anew takes its origin from some innovating cause other than
itself: "That which comes to be anew must take its origin from some innovating
cause; since nothing brings itself from potency to act, or from non-being to
being." Aquinas gives it as the reason why, "if the world and motion have a first
beginning, some cause must clearly be posited to account for this origin".

"Innovating cause" is read as a cause, other than the thing, from which its
coming to be takes its origin. What that cause is (God) is not part of the
reading.

Source: Thomas Aquinas, *Summa contra Gentiles* I.13 [30] (Pegis translation).
-/
def WhatComesToBeAnewHasInnovatingCauseReading {Being : Sort u} {Time : Sort v}
    (IsAt : Being → Time → Prop) (Before : Time → Time → Prop)
    (CausesOrigin : Being → Being → Prop) : Prop :=
  ∀ x, ComesToBeAnew IsAt Before x → ∃ c, c ≠ x ∧ CausesOrigin c x

/-- Something has an innovating cause: some being's coming to be takes its
origin from a cause other than it. The conclusion of the finite-past horn. -/
def SomethingHasInnovatingCause {Being : Sort u}
    (CausesOrigin : Being → Being → Prop) : Prop :=
  ∃ x c, c ≠ x ∧ CausesOrigin c x

end TruthCore.Latin.Aquinas.SummaContraGentiles
