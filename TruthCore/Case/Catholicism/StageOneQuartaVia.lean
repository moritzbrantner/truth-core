import TruthCore.Case.Catholicism.StageOneBridges
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3QuartaVia

/-!
Stage-1 statements that connect the *prima via*'s first mover moved by none
(#151) with the *quarta via*'s maximal being (ST I q.2 a.3, fourth way; #147).
Both are conclusions of verified results, not readings of a sentence.
-/

namespace TruthCore.Case.Catholicism

open TruthCore.Latin.Aquinas.SummaTheologiae (IsMaximumIn)

universe v w

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
