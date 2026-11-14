module

public import TruthCore.Causality.TermSenseForks

/-! ## Productive interpretation of an originating cause

`CausesOrigin` is an untimed, unconstrained field of `CauseFrame`. This OPEN
analyst bridge says only that each selected origin edge is realized by an
occurring exercise of the source which produces the target's existence. It
does not define `CausesOrigin`, assert that every cause is productive in this
sense, or establish that the relation has any real-world instances.

The bearer, exercise, and product are kept separate. An origin edge mediated
by a different bearer's exercise cannot be used as a self-origin edge. The
existential-priority laws remain four separate premises of the consuming
argument rather than properties silently inserted into this definition.
-/

@[expose] public section

namespace TruthCore.Causality.OriginExerciseBridge

open TruthCore.Causality.TermSenseForks

/-- Each `CAUSE_4` originating-cause edge is realized by some occurring
exercise borne by that very originator and producing that target's existence.
This is an OPEN interpretation bridge from `CausesOrigin` to the independent
existential-production vocabulary, not a source reading or a logical truth. -/
def OriginHasProductiveExercise {Being Respect Exercise : Type}
    (F : CauseFrame Being Respect) (Occurs : Exercise → Prop)
    (bearer : Exercise → Being) (produces : Exercise → Being → Prop) : Prop :=
  ∀ c x, F.CausesOrigin c x →
    ∃ a, Occurs a ∧ bearer a = c ∧ produces a x

end TruthCore.Causality.OriginExerciseBridge
