import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3

/-!
Source-derived readings from Thomas Aquinas, *Summa theologiae* I q.3 a.1 co.
(*utrum Deus sit corpus*).

A first mover moved by none is written out as
`(∃ x r, MovesIn f x r) ∧ ∀ r, ¬ MovedIn f r`, the body of the *prima via*
conclusion; it is definitionally `TruthCore.Case.Catholicism.IsFirstUnmovedMover`.

The vocabulary of the *prima via* (`Being`, `Respect`, `MovedIn`, `MovesIn`,
`InPotency`, `InAct`; see `Question2.Article3`) is reused and extended:

* `Body b` — `b` is a body.
* `PriorSimply y x` — `y` is prior to `x` simply (*simpliciter*), not merely in
  time: `x`'s being in act depends on `y`. This is a different relation from
  moving: a being can be simply posterior to another without being moved by it
  at present.

Aquinas gives three proofs that God is not a body. The first (*primo*) argues
from the *prima via* alone; the second (*secundo*) argues from the priority of
act over potency to "the first being is in no way in potency". The third
(*tertio*, from nobility) is not formalized here.

Source witness: SCTA diplomatic TEI of the Leonine edition, vol. 4 (Rome 1888),
`scta-texts/TAca84`, passage `AQUINAS-ST-I-Q3-A1`.
-/

namespace TruthCore.Latin.Aquinas.SummaTheologiae

universe u v

/-- `f` is pure act: it is in potency in no respect (*nullo modo in potentia*;
q.3 a.2 co. glosses it as *purus actus, non habens aliquid de
potentialitate*). -/
def PureAct {Being : Sort u} {Respect : Sort v}
    (InPotency : Being → Respect → Prop) (f : Being) : Prop :=
  ∀ r, ¬ InPotency f r

/-- No body moves without being moved (*nullum corpus movet non motum: ut patet
inducendo per singula*).

Every body that moves something is itself moved in some respect. Aquinas
supports it by induction over cases, not by demonstration.

Its conclusion, that no first mover moved by none is a body (*Ostensum est
autem supra quod Deus est primum movens immobile. Unde manifestum est quod Deus
non est corpus*), is part of `FirstUnmovedMoverIsSimpleReading`.

Source: Thomas Aquinas, *Summa theologiae* I q.3 a.1 co., first proof.
-/
def NoBodyMovesUnlessMovedReading {Being : Sort u} {Respect : Sort v}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (Body : Being → Prop) : Prop :=
  ∀ b, Body b → (∃ x r, MovesIn b x r) → ∃ r, MovedIn b r

/-- Act is simply prior to potency (*licet enim in uno et eodem quod exit de
potentia in actum, prius sit potentia quam actus tempore, simpliciter tamen
actus prior est potentia: quia quod est in potentia, non reducitur in actum nisi
per ens actu*).

Whatever is in potency in a respect is simply posterior to some being that is
in act in that respect. The premise does not say that the prior being is
distinct; that follows from `NotActAndPotencyInSameRespectReading`. It does not
say that the potency is being actualized now, so it does not make every potency
a present being-moved.

Source: Thomas Aquinas, *Summa theologiae* I q.3 a.1 co., second proof.
-/
def ActSimplyPriorToPotencyReading {Being : Sort u} {Respect : Sort v}
    (InAct InPotency : Being → Respect → Prop)
    (PriorSimply : Being → Being → Prop) : Prop :=
  ∀ x r, InPotency x r → ∃ y, InAct y r ∧ PriorSimply y x

/-- `f` is the first being (*primum ens*): no being other than `f` is simply
prior to it. -/
def IsFirstBeing {Being : Sort u}
    (PriorSimply : Being → Being → Prop) (f : Being) : Prop :=
  ∀ y, PriorSimply y f → y = f

/-- The first being must be in act and in no way in potency (*necesse est id quod
est primum ens, esse in actu, et nullo modo in potentia*).

Only the "in no way in potency" part is formalized; it is what q.3 a.2, a.4 and
a.7 use.

Source: Thomas Aquinas, *Summa theologiae* I q.3 a.1 co., second proof.
-/
def FirstBeingIsInNoWayInPotencyReading {Being : Sort u} {Respect : Sort v}
    (InPotency : Being → Respect → Prop)
    (PriorSimply : Being → Being → Prop) : Prop :=
  ∀ f, IsFirstBeing PriorSimply f → PureAct InPotency f

/-- The first mover moved by none is the first being (*Ostensum est autem supra
quod Deus est primum ens*).

Aquinas cites this as already shown (in q.2 a.3). The pinned q.2 a.3 text of the
*prima via* does not state it: the *prima via* shows only that nothing moves the
first mover, and `PriorSimply` is not moving. So the statement is an explicit
open premise of the route from the *prima via* to pure act, not a consequence of
#151's premises. Reading "Deus" here as the *prima via*'s first mover is an
interpretive choice; the back-reference may instead be to the fourth way
(*aliquid quod est maxime ens*).

Source: Thomas Aquinas, *Summa theologiae* I q.3 a.1 co., second proof.
-/
def FirstUnmovedMoverIsFirstBeingReading {Being : Sort u} {Respect : Sort v}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (PriorSimply : Being → Being → Prop) : Prop :=
  ∀ f, ((∃ x r, MovesIn f x r) ∧ ∀ r, ¬ MovedIn f r) → IsFirstBeing PriorSimply f

end TruthCore.Latin.Aquinas.SummaTheologiae
