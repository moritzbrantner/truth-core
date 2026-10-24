/-!
Notions in which the shared metaethical questions of #183 are put, and the
propositions that answer them. They are definitions of what the questions ask,
not premises of any theory: each theory's answer is a separate, sourced reading.

* `Q-MORAL-ERROR`: can someone be in error about a moral matter? To err about
  `φ` is to accept `φ` when `φ` has a truth value and is not true: a false
  belief, not a change of feeling.
* `Q-MORAL-DISAGREEMENT`: is a moral disagreement a contradiction? Two people
  genuinely contradict each other about `φ` when one accepts it, the other
  rejects it, and `φ` has a truth value, so that they cannot both be right: a
  disagreement in belief, not merely one of attitude ("I like it" vs.
  "I don't").
* `Q-MORAL-PROGRESS` (correction of an earlier moral error) is answered in
  prose in `TruthCore.Comparison.MoralError`; on the cognitive reading it
  presupposes moral error.
-/

namespace TruthCore.Metaethics

universe u v

/-- `x` errs about `φ`: accepts it, though it has a truth value and is not
true. -/
def Errs {Agent : Sort u} {Sentence : Sort v}
    (Accepts : Agent → Sentence → Prop) (TruthApt Holds : Sentence → Prop)
    (x : Agent) (φ : Sentence) : Prop :=
  Accepts x φ ∧ TruthApt φ ∧ ¬ Holds φ

/-- `x` and `y` genuinely contradict each other about `φ`: `x` accepts it, `y`
rejects it, and it has a truth value. -/
def GenuinelyContradict {Agent : Sort u} {Sentence : Sort v}
    (Accepts Rejects : Agent → Sentence → Prop) (TruthApt : Sentence → Prop)
    (x y : Agent) (φ : Sentence) : Prop :=
  Accepts x φ ∧ Rejects y φ ∧ TruthApt φ

/-- No one errs about any moral sentence. -/
def NoMoralError {Agent : Sort u} {Sentence : Sort v}
    (Accepts : Agent → Sentence → Prop) (Moral TruthApt Holds : Sentence → Prop) : Prop :=
  ∀ x φ, Moral φ → ¬ Errs Accepts TruthApt Holds x φ

/-- No two people genuinely contradict each other about a moral sentence. -/
def NoGenuineMoralContradiction {Agent : Sort u} {Sentence : Sort v}
    (Accepts Rejects : Agent → Sentence → Prop) (Moral TruthApt : Sentence → Prop) : Prop :=
  ∀ x y φ, Moral φ → ¬ GenuinelyContradict Accepts Rejects TruthApt x y φ

/-- Someone errs about some moral sentence. -/
def SomeMoralError {Agent : Sort u} {Sentence : Sort v}
    (Accepts : Agent → Sentence → Prop) (Moral TruthApt Holds : Sentence → Prop) : Prop :=
  ∃ x φ, Moral φ ∧ Errs Accepts TruthApt Holds x φ

end TruthCore.Metaethics
