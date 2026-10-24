import TruthCore.Case.Catholicism.StageOneBridges
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3QuartaVia

/-!
Stage-1 statements that connect the *prima via*'s first mover moved by none
(#151) with the *quarta via*'s maximal being (ST I q.2 a.3, fourth way; #147).
`FirstUnmovedMoverIsMaximeEns`, `FirstUnmovedMoverHasEveryPerfectionOfThings`,
`MaximeEnsIsGod` and `AtMostOneMaximeEns` are conclusions of verified results.
`SimplyPriorIsCauseOfBeing` and `GodNamesTheUniqueMaximeEns` are open premises:
no source sentence asserts them in this form, and each states exactly one link
that the derivation needs.
-/

namespace TruthCore.Case.Catholicism

open TruthCore.Latin.Aquinas.SummaTheologiae (IsMaximumIn CausesAllInGenus)

universe v w

/-- Whatever is maximal in being is God, in the sense in which ST I q.105 a.5 speaks
of God (`God`). Introduced as an open premise (#173); derived in result
`AQUINAS-ST-I-Q2-A3-MAXIME-ENS-IS-GOD` (#143, 2026-10-24) from the uniqueness of
the maximum in being (`AtMostOneMaximeEns`) and the explicit nominal definition
`GodNamesTheUniqueMaximeEns` (open premise, supported by q.13 a.8 ad 2 and
*et hoc dicimus Deum*). The
identification stays nominal: it rests on the name "God" having one use in
q.2 a.3 and q.105 a.5, which is the content of that definition. -/
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

/-- There is at most one maximum in being: any two beings that are each maximal in
being (`IsMaximumIn InAct MoreIn esse`: each has being, and nothing is more a
being than either) are the same. Derived in result
`AQUINAS-ST-I-Q2-A3-AT-MOST-ONE-MAXIME-ENS` from the *quarta via*'s genus
principle and *Metaphysics* II.1; it is not a source reading. -/
def AtMostOneMaximeEns {Being : Sort v} {Respect : Sort w}
    (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop) (esse : Respect) : Prop :=
  ∀ m m', IsMaximumIn InAct MoreIn esse m → IsMaximumIn InAct MoreIn esse m' → m = m'

/-- The name "God" applies to the only being that is maximal in being and causes the
being of every other being: such a being is the one the *Summa* calls God
(q.105 a.5). Open premise (candidate `AQUINAS-NOMINAL-DESCRIPTION-OF-GOD-SUFFICES`).

It is **not** a reading of the sources, and the source descriptions do not state
it. q.13 a.8 ad 2 gives the name's nominal definition as *aliquid … supra omnia
existens, quod est principium omnium, et remotum ab omnibus*, and the *quarta
via*'s *et hoc dicimus Deum* names the cause of being, goodness *and every
perfection*. This premise keeps only "maximal in being" (above all) and "cause of
being of all others" (principle of all). It drops *remotum ab omnibus* and the
causation of goodness and every perfection. Dropping conjuncts from the antecedent
of a sufficient description strengthens it, so this premise asserts that the
reduced description already suffices for the name to apply. The two passages
support it (`supports` relations) without stating it. To discharge it, show that
the unique maximum in being also has the omitted properties.

The uniqueness clause reads the singular *hoc* / *aliquid … quod est principium
omnium* as a definite description that applies only when exactly one being fits.
By q.13 a.9 the name is communicable by its *ratio*, so uniqueness is a condition
of application here, not an assertion. The definition stays nominal, as in
q.2 a.2 ad 2: it fixes what the name signifies, not what God is. -/
def GodNamesTheUniqueMaximeEns {Being : Sort v} {Respect : Sort w}
    (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (God : Being → Prop) : Prop :=
  ∀ m, IsMaximumIn InAct MoreIn esse m → CausesAllInGenus InAct CausesIn esse m →
    (∀ m', IsMaximumIn InAct MoreIn esse m' → m' = m) → God m

end TruthCore.Case.Catholicism
