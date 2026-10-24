import TruthCore.Case.Catholicism.StageOne
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article1

/-!
Open bridges of the stage-1 route from the *prima via* to pure act and
uniqueness (#165). Each is a premise of a verified result, kept in the case
layer because no source sentence asserts it of every first mover moved by none.
Aquinas' corresponding sentences are back-references about God (ST I q.3 a.1:
*Deus est primum ens*; q.11 a.3: *Deus comprehendit in se totam perfectionem
essendi*); turning them into statements about the *prima via*'s mover is exactly
the identification still to be argued.

`PriorSimply` is the simple priority of ST I q.3 a.1
(`TruthCore.Latin.Aquinas.SummaTheologiae.ActSimplyPriorToPotencyReading`).
-/

namespace TruthCore.Case.Catholicism

open TruthCore.Latin.Aquinas.SummaTheologiae (IsFirstBeing)

universe v w

/-- Every first mover moved by none is the first being: nothing other than it is
simply prior to it. Open bridge (candidate
`AQUINAS-FIRST-MOVER-IS-FIRST-BEING`). Not entailed by the *prima via*: see
`TruthCore.Results.Aquinas.SummaTheologiae.FirstMoverPureAct.firstWayDoesNotYieldPureAct`. -/
def FirstUnmovedMoverIsFirstBeing {Being : Sort v} {Respect : Sort w}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (PriorSimply : Being → Being → Prop) : Prop :=
  ∀ f, IsFirstUnmovedMover MovedIn MovesIn f → IsFirstBeing PriorSimply f

/-- Every first mover moved by none is in act, formally or eminently, in every
respect. Open bridge (candidate `AQUINAS-ST-I-Q4-A1-A2`). -/
def FirstUnmovedMoverHasEveryPerfection {Being : Sort v} {Respect : Sort w}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (InAct : Being → Respect → Prop) : Prop :=
  ∀ f, IsFirstUnmovedMover MovedIn MovesIn f → ∀ r, InAct f r

/-- Any two first movers moved by none are either the same or distinct. An
instance of excluded middle, like `FirstUnmovedMoverExistsOrNot`, stated as an
explicit premise rather than taken as an axiom. An instance of
`TruthCore.Logic.ExcludedMiddle` (result
`CATHOLICISM-FIRST-UNMOVED-MOVERS-IDENTICAL-OR-DISTINCT-FROM-EM`), marked
`self_evident` as such in #167. It lets the reductio of ST I q.11 a.3 conclude
a plain identity. -/
def FirstUnmovedMoversIdenticalOrDistinct {Being : Sort v} {Respect : Sort w}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop) : Prop :=
  ∀ f g, IsFirstUnmovedMover MovedIn MovesIn f →
    IsFirstUnmovedMover MovedIn MovesIn g → f = g ∨ f ≠ g

end TruthCore.Case.Catholicism
