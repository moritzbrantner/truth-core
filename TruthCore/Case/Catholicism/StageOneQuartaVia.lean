import TruthCore.Case.Catholicism.StageOneBridges
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3QuartaVia

/-!
Stage-1 statements that connect the *prima via*'s first mover moved by none
(#151) with the *quarta via*'s maximal being (ST I q.2 a.3, fourth way; #147).
`FirstUnmovedMoverIsMaximeEns` and `FirstUnmovedMoverHasEveryPerfectionOfThings`
are conclusions of verified results. `MaximeEnsIsGod` and
`SimplyPriorIsCauseOfBeing` are open premises: no source sentence asserts them in
this form, and each states exactly one link that the derivation needs.
-/

namespace TruthCore.Case.Catholicism

open TruthCore.Latin.Aquinas.SummaTheologiae (IsMaximumIn)

universe v w

/-- Whatever is maximal in being is God, in the sense in which ST I q.105 a.5 speaks
of God (`God`). Open premise (candidate `AQUINAS-MAXIME-ENS-IS-GOD`). The
*quarta via* ends *et hoc dicimus Deum*, which supports it but is a nominal
remark about the cause of being and every perfection; reading it as identifying
that cause with the one q.105 a.5 says applies every created agent to act is the
step still to be argued. -/
def MaximeEnsIsGod {Being : Sort v} {Respect : Sort w}
    (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop) (esse : Respect)
    (God : Being → Prop) : Prop :=
  ∀ m, IsMaximumIn InAct MoreIn esse m → God m

/-- What is simply prior to a thing (ST I q.3 a.1, `PriorSimply`) is a cause of its
being. Open premise (candidate `AQUINAS-SIMPLE-PRIORITY-AS-CAUSE-OF-BEING`). #166
reads simple priority as the dependence of a thing's being in act on a being in
act; q.3 a.1 states it for an actualizer in some respect, so the step to a cause
of *esse* is not supplied by that text. -/
def SimplyPriorIsCauseOfBeing {Being : Sort v} {Respect : Sort w}
    (PriorSimply : Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect) : Prop :=
  ∀ y x, PriorSimply y x → CausesIn y x esse

/-- Every first mover moved by none is the maximal being (*maxime ens*) of the
*quarta via*: it is identical with every being that is maximal in being. Derived
in result `AQUINAS-ST-I-Q2-A3-FIRST-MOVER-IS-MAXIME-ENS`. -/
def FirstUnmovedMoverIsMaximeEns {Being : Sort v} {Respect : Sort w}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop) (esse : Respect) : Prop :=
  ∀ f, IsFirstUnmovedMover MovedIn MovesIn f →
    ∀ m, IsMaximumIn InAct MoreIn esse m → f = m

/-- Every first mover moved by none has every perfection found in things: whatever
any being is in act in, it is in act in too, formally or eminently (ST I q.4 a.2:
*in Deo sunt perfectiones omnium rerum*). Weaker than
`FirstUnmovedMoverHasEveryPerfection`, which asks for act in every respect, also
in respects that no being has. Derived in result
`AQUINAS-ST-I-Q4-A2-FIRST-MOVER-HAS-PERFECTIONS-OF-THINGS`. -/
def FirstUnmovedMoverHasEveryPerfectionOfThings {Being : Sort v} {Respect : Sort w}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (InAct : Being → Respect → Prop) : Prop :=
  ∀ f, IsFirstUnmovedMover MovedIn MovesIn f → ∀ x r, InAct x r → InAct f r

end TruthCore.Case.Catholicism
