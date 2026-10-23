import TruthCore.Case.Catholicism.Root
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3

/-!
The gap between the prima via (#151) and stage 1, "God exists" (issue #156).

The prima via result concludes only that a first mover moved by none cannot be
lacking (`FirstUnmovedMoverCannotBeLackingReading`). That is weaker than "God
exists" in four ways, each recorded here as its own open statement:

* the result is a double negation, and turning it into an existential is a
  use of excluded middle, made explicit as a premise rather than an axiom;
* uniqueness: there is at most one first unmoved mover;
* pure act: a first unmoved mover is pure act, with no potency at all;
* identification: a unique first unmoved mover that is pure act is God, in
  the sense of the God of classical theism (`IsGod`). This is stronger than
  the nominal *et hoc omnes intelligunt Deum* (claim
  `AQUINAS-ST-I-Q2-A3-UNDERSTOOD-AS-GOD-A`), which only reports how the name
  is used, so it is a separate statement and not a reading of that clause.

The vocabulary reuses the prima via parameters `MovedIn` and `MovesIn` and adds
`PureAct` and `IsGod`, all as parameters.
-/

namespace TruthCore.Case.Catholicism

universe v w

/-- `f` is a first mover moved by none: it moves something and is itself moved
in no respect. The body of `FirstUnmovedMoverCannotBeLackingReading`, named. -/
def IsFirstUnmovedMover {Being : Sort v} {Respect : Sort w}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop) (f : Being) : Prop :=
  (∃ x r, MovesIn f x r) ∧ ∀ r, ¬ MovedIn f r

/-- Excluded middle for one proposition: either there is a first unmoved mover
or there is none. Open premise; a candidate for a `self_evident` marking from
Aristotle, *Metaphysics* IV.7 (candidate `ARIST-MET-IV-7-EXCLUDED-MIDDLE`). -/
def FirstUnmovedMoverExistsOrNot {Being : Sort v} {Respect : Sort w}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop) : Prop :=
  (∃ f, IsFirstUnmovedMover MovedIn MovesIn f) ∨
    ¬ ∃ f, IsFirstUnmovedMover MovedIn MovesIn f

/-- There is a first mover moved by none. Intermediate conclusion. -/
def ThereIsAFirstUnmovedMover {Being : Sort v} {Respect : Sort w}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop) : Prop :=
  ∃ f, IsFirstUnmovedMover MovedIn MovesIn f

/-- Uniqueness gap: there is at most one first unmoved mover. Derived in result
`AQUINAS-ST-I-Q11-A3-ONE-FIRST-MOVER` (ST I q.11 a.3) from open bridges in
`StageOneBridges`. -/
def AtMostOneFirstUnmovedMover {Being : Sort v} {Respect : Sort w}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop) : Prop :=
  ∀ f g, IsFirstUnmovedMover MovedIn MovesIn f →
    IsFirstUnmovedMover MovedIn MovesIn g → f = g

/-- Pure-act gap: every first unmoved mover is pure act. Derived in result
`AQUINAS-ST-I-Q3-A1-FIRST-MOVER-PURE-ACT` (ST I q.3 a.1), with `PureAct InPotency`
for `PureAct`, from the open first-being bridge in `StageOneBridges`. -/
def FirstUnmovedMoverIsPureAct {Being : Sort v} {Respect : Sort w}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop) (PureAct : Being → Prop) : Prop :=
  ∀ f, IsFirstUnmovedMover MovedIn MovesIn f → PureAct f

/-- Identification gap: a first unmoved mover that is pure act and the only
first unmoved mover is God. Open premise (candidate
`AQUINAS-ST-I-Q3-Q26-IDENTIFICATION`). -/
def UniquePureActFirstMoverIsGod {Being : Sort v} {Respect : Sort w}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (PureAct IsGod : Being → Prop) : Prop :=
  ∀ f, IsFirstUnmovedMover MovedIn MovesIn f → PureAct f →
    (∀ g, IsFirstUnmovedMover MovedIn MovesIn g → g = f) → IsGod f

end TruthCore.Case.Catholicism
