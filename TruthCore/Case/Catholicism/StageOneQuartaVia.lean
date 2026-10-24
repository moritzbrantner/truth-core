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
support it (`supports` relations) without stating it. Version (b) of its
discharge (`AQUINAS-REDUCED-DESCRIPTION-OF-GOD-SUFFICES`) shows that the unique
maximum in being also has the omitted properties, and so derives it from the
fuller `GodNamesTheFullyDescribedPrinciple` below.

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

/-! ## The fuller description (owner decision on #143, 2026-10-24)

Two versions of the nominal definition are kept side by side, each its own
statement: the reduced `GodNamesTheUniqueMaximeEns` above
(`STMT-GOD-NAMES-THE-UNIQUE-MAXIME-ENS`) and the fuller
`GodNamesTheFullyDescribedPrinciple` below
(`STMT-GOD-NAMES-THE-FULLY-DESCRIBED-PRINCIPLE`), which keeps every condition
the sources give. Version (a) proves that the unique maximum in being meets the
fuller description (`AQUINAS-ST-I-Q2-A3-MAXIME-ENS-IS-GOD-VIA-FULL-DESCRIPTION`).
Version (b) defends the reduced one: given the fuller definition, the reduced
description already suffices (`AQUINAS-REDUCED-DESCRIPTION-OF-GOD-SUFFICES`). -/

/-- `c` causes every perfection of every other being: whatever another being
is in act in, `c` causes it to be so (*causa ... bonitatis, et cuiuslibet
perfectionis*, quarta via; *omnes perfectiones desideratae effluunt ab eo,
sicut a prima causa*, q.6 a.2). Like `CausesAllInGenus`, it leaves `c` itself
out. -/
def CausesEveryPerfectionOfOthers {Being : Sort v} {Respect : Sort w}
    (InAct : Being → Respect → Prop)
    (CausesIn : Being → Being → Respect → Prop) (c : Being) : Prop :=
  ∀ x r, x ≠ c → InAct x r → CausesIn c x r

/-- `m` is remote from all (*remotum ab omnibus*, q.13 a.8 ad 2): it enters into
the composition of nothing, as neither part, matter nor form of anything (q.3
a.8). This reads the way of remotion through q.3 a.8, the article that denies
God any composition with other things. Other readings of *remotum* (for
example, transcendence of every genus, q.3 a.5) are possible and are not
excluded by this one. -/
def RemoteFromAll {Being : Sort v} (ComponentOf : Being → Being → Prop) (m : Being) : Prop :=
  ∀ x, ¬ ComponentOf m x

/-- The cause of a thing's being causes each of its perfections: if `c` causes
`x`'s being and `x` is in act in `r`, then `c` causes `x`'s being in act in `r`.
Open premise. It is supported, not stated, by q.4 a.2 (every perfection of a
thing pertains to its perfection of being: *secundum hoc enim aliqua perfecta
sunt, quod aliquo modo esse habent*) and q.6 a.2 (all perfections flow from God
as from their first cause). -/
def CauseOfBeingCausesEveryPerfection {Being : Sort v} {Respect : Sort w}
    (InAct : Being → Respect → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect) : Prop :=
  ∀ c x r, CausesIn c x esse → InAct x r → CausesIn c x r

/-- The fuller nominal definition: the name "God" applies to the only being
that is maximal in being (*supra omnia existens*), causes the being of every
other being (*principium omnium*), causes every perfection of every other being
(*causa ... cuiuslibet perfectionis*, quarta via) and enters into the
composition of nothing (*remotum ab omnibus*). Open premise, but closer to the
sources than `GodNamesTheUniqueMaximeEns`: it drops none of the conditions of
q.13 a.8 ad 2 and *et hoc dicimus Deum*, so it is weaker.

As in the reduced version, the uniqueness clause reads the singular as a
definite description. The definition fixes what the name signifies (q.2 a.2
ad 2), so a being that meets it is God in the proper sense of the name, not
merely called God: it is through this premise that the *Summa*'s God and the
skeleton's `IsGod` are the same predicate in the stage-1 route
`CATHOLICISM-STAGE1-VIA-FULL-DESCRIPTION`. -/
def GodNamesTheFullyDescribedPrinciple {Being : Sort v} {Respect : Sort w}
    (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (ComponentOf : Being → Being → Prop) (God : Being → Prop) : Prop :=
  ∀ m, IsMaximumIn InAct MoreIn esse m → CausesAllInGenus InAct CausesIn esse m →
    CausesEveryPerfectionOfOthers InAct CausesIn m → RemoteFromAll ComponentOf m →
    (∀ m', IsMaximumIn InAct MoreIn esse m' → m' = m) → God m

end TruthCore.Case.Catholicism
