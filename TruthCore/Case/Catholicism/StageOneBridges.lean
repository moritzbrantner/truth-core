import TruthCore.Case.Catholicism.StageOne
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article1

/-!
Bridges of the stage-1 route from the *prima via* to pure act and
uniqueness (#165). Each is a premise of a verified result, kept in the case
layer because no source sentence asserts it of every first mover moved by none.
Aquinas' corresponding sentences are back-references about God (ST I q.3 a.1:
*Deus est primum ens*; q.11 a.3: *Deus comprehendit in se totam perfectionem
essendi*); turning them into statements about the *prima via*'s mover is exactly
the identification still to be argued.
#147 argues that identification through the *quarta via*
(`TruthCore.Case.Catholicism.FirstUnmovedMoverIsMaximeEns`), which derives the
first-being bridge and a weaker form of the every-perfection bridge.

`PriorSimply` is the simple priority of ST I q.3 a.1
(`TruthCore.Latin.Aquinas.SummaTheologiae.ActSimplyPriorToPotencyReading`).
-/

namespace TruthCore.Case.Catholicism

open TruthCore.Latin.Aquinas.SummaTheologiae (IsFirstBeing)

universe v w

/-- Every first mover moved by none is the first being: nothing other than it is
simply prior to it. Not entailed by the *prima via*: see
`TruthCore.Results.Aquinas.SummaTheologiae.FirstMoverPureAct.firstWayDoesNotYieldPureAct`.
Derived through the *quarta via* (#147) in result
`AQUINAS-ST-I-Q2-A3-FIRST-MOVER-IS-FIRST-BEING`, from sourced premises that
include ST I q.105 a.5 (translation basis) and *Metaphysics* II.1. -/
def FirstUnmovedMoverIsFirstBeing {Being : Sort v} {Respect : Sort w}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (PriorSimply : Being → Being → Prop) : Prop :=
  ∀ f, IsFirstUnmovedMover MovedIn MovesIn f → IsFirstBeing PriorSimply f

/-- Every first mover moved by none is in act, formally or eminently, in every
respect. Open bridge (candidate `AQUINAS-ST-I-Q4-A1-A2`: the second proof of
q.4 a.2). Its weaker form for the perfections found in things,
`FirstUnmovedMoverHasEveryPerfectionOfThings`, is derived (#147), and uniqueness
now also follows without it (`AQUINAS-ST-I-Q2-A3-ONE-FIRST-MOVER-VIA-MAXIME-ENS`). -/
def FirstUnmovedMoverHasEveryPerfection {Being : Sort v} {Respect : Sort w}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (InAct : Being → Respect → Prop) : Prop :=
  ∀ f, IsFirstUnmovedMover MovedIn MovesIn f → ∀ r, InAct f r

/-- Any two first movers moved by none are either the same or distinct. An
instance of excluded middle, like `FirstUnmovedMoverExistsOrNot`, stated as an
explicit premise rather than taken as an axiom. An instance of
`TruthCore.Logic.ExcludedMiddle` (result
`CATHOLICISM-FIRST-UNMOVED-MOVERS-IDENTICAL-OR-DISTINCT-FROM-EM`, a
transcription), whose general principle is marked `self_evident` in #167; still
an open premise under invariant 16. It lets the reductio of ST I q.11 a.3 conclude
a plain identity. -/
def FirstUnmovedMoversIdenticalOrDistinct {Being : Sort v} {Respect : Sort w}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop) : Prop :=
  ∀ f g, IsFirstUnmovedMover MovedIn MovesIn f →
    IsFirstUnmovedMover MovedIn MovesIn g → f = g ∨ f ≠ g

end TruthCore.Case.Catholicism
