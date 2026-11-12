module

public import TruthCore.Causality.DeiFiliusLivingSelfOperation

/-! *Vivus* from the nine: the weakest versions of the self-operation premises
that the root-reaching living route needs

The living route to the restated sufficiency (`NineSufficeForDeiFilius`, result
`08bf7a13`) uses `STMT-PURE-ACT-LIVES` (`PureActLivesReading`: every pure act lives
at some time of the duration frame, LIVING_2), itself derived (result
`PURE-ACT-LIVES-FROM-SELF-OPERATION`) from the universal `STMT-PURE-ACT-OPERATES`
(`PureActOperates`: every pure act operates from itself). The route applies them
at one kind of being only: a being with the nine stage-two attributes (simple,
universally perfect, supremely good, the one GOD_4, infinite, altogether
immutable, eternal, with intellect and will). Altogether immutability is pure
act, so it is a restriction, not a change of subject.

This module states the restricted (weak) versions, scoped exactly to what the
sufficiency quantifies over:

* `NineOperate`: whatever has the nine operates from itself;
* `NineLiveSomeTime`: whatever has the nine lives at some time of the frame
  (LIVING_2, `LivesSomeTime`).

The strong versions entail them (the immutability conjunct is pure act); the
converse fails (`Control.Controls` parts 1 and 2, where an inert pure act with
no intellect satisfies the weak versions and falsifies the strong ones). The
scope worry recorded in attempt `6683acc4` (a causally inert abstract object, if
the `Being` domain contains one, would be a pure act that does not operate) does
not touch the weak versions: such an object would lack the nine (intellect,
will, causing every perfection of other things).

Cost of the restriction, stated plainly. The nine include HAS_INTELLECT_1, so the
weak versions speak only of beings with intellect (and the other eight). The
living route therefore no longer covers non-intellectual pure acts, and the
source warrant (q.18 a.3: life grounded in God's being his own understanding)
remains the warrant through intellect it was. Formally, the route still does not
presuppose the intellect bridge `IntellectualIsLiving` (8d2ac441), not even its
restriction to pure acts: `Control.Controls` part 4 has the weak bundle and the
sense bridge true where an intellectual pure act does not live.

Analyst formulations, attribution deferred. -/

@[expose] public section

namespace TruthCore.Causality.DeiFiliusLivingNineScope

open TruthCore.Case.Catholicism
open TruthCore.Latin.Aquinas.SummaTheologiae (PureAct)
open TruthCore.Causality.DeiFiliusAttributeField

/-- The nine stage-two attributes at one being, with the parameters the restated
sufficiency uses (`NineSufficeForDeiFilius` with `σ.IsGod` for `IsGod`). A
reducible abbreviation of `NineClassicalAttributes`, so the weak versions below
are literally restrictions to its antecedent. -/
abbrev HasTheNine {Being Respect : Type} (InAct GoodIn InPotency : Being → Respect → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (IsGod Composite Infinite Eternal HasIntellect HasWill : Being → Prop) (g : Being) : Prop :=
  NineClassicalAttributes (IsSimple Composite) (IsPerfect InAct)
    (IsSupremelyGood InAct GoodIn CausesIn esse) (IsTheOneGod IsGod)
    Infinite (IsImmutable InPotency) Eternal HasIntellect HasWill g

/-- Weak version of `STMT-PURE-ACT-OPERATES`: whatever has the nine operates from
itself (`Operates`, the primitive immanent operation of `SelfOperationLife`).
Open premise, analyst formulation. Since altogether immutability is pure act,
it is `PureActOperates` restricted to beings that also have the other eight. -/
def NineOperate {Being Respect : Type} (InAct GoodIn InPotency : Being → Respect → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (IsGod Composite Infinite Eternal HasIntellect HasWill : Being → Prop)
    (Operates : Being → Prop) : Prop :=
  ∀ g, HasTheNine InAct GoodIn InPotency CausesIn esse IsGod Composite Infinite Eternal
    HasIntellect HasWill g → Operates g

/-- Weak version of `STMT-PURE-ACT-LIVES`: whatever has the nine lives at some time
of the duration frame (LIVING_2, `LivesSomeTime`). Not LIVING_1: the passage to
the timeless primitive is the separate restricted sense bridge
`PureActLifeAtSomeTimeIsLiving`. -/
def NineLiveSomeTime {Being Respect Time : Type} (InAct GoodIn InPotency : Being → Respect → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (IsGod Composite Infinite Eternal HasIntellect HasWill : Being → Prop)
    (LivesAt : Being → Time → Prop) : Prop :=
  ∀ g, HasTheNine InAct GoodIn InPotency CausesIn esse IsGod Composite Infinite Eternal
    HasIntellect HasWill g → LivesSomeTime LivesAt g

namespace Control

/-- Two beings: `true` alone is GOD_4 and has intellect; nothing is in potency;
everything is in act and causes everything; nothing is composite. -/
def inAct (_ : Bool) (_ : Unit) : Prop := True
def causes (_ _ : Bool) (_ : Unit) : Prop := True
def noPotency (_ : Bool) (_ : Unit) : Prop := False
def isTrue (g : Bool) : Prop := g = true
def yes (_ : Bool) : Prop := True
def no (_ : Bool) : Prop := False
def onlyTrueAt (g : Bool) (_ : Unit) : Prop := g = true

/-- The nine on this interpretation, with intellect given by `HasIntellect`. -/
abbrev Nine (HasIntellect : Bool → Prop) (g : Bool) : Prop :=
  HasTheNine inAct inAct noPotency causes () isTrue no yes yes HasIntellect yes g

/-- Checked interpretations on two beings (`Bool`), one respect and one time:

1. strictness for operation: `true` has the nine and operates; `false` is a pure
   act with no intellect and no operation (an inert pure act, the shape of the
   abstract-object scope worry). `NineOperate` holds and `PureActOperates`
   fails;
2. strictness for life: with life only at `true`, `NineLiveSomeTime` holds and
   `PureActLivesReading` fails;
3. the weak lives premise is not vacuous: some being has the nine and lives at
   some time;
4. the weak route does not presuppose the intellect bridge, nor its restriction
   to pure acts: with both beings intellectual and only `true` LIVING_1,
   `NineLiveSomeTime` and the restricted sense bridge hold, while `false` is an
   intellectual pure act that does not live (so `IntellectualIsLiving` fails);
5. sense-mixing control: with nothing LIVING_1, `NineLiveSomeTime` holds and
   `true` has the nine and is LIVING_2 without being LIVING_1, so the weak life
   premise alone does not give the living conjunct (the sense bridge is
   needed). -/
def Controls : Prop :=
  (NineOperate inAct inAct noPotency causes () isTrue no yes yes isTrue yes isTrue ∧
    ¬ TruthCore.Causality.SelfOperationLife.PureActOperates noPotency isTrue ∧
    Nine isTrue true ∧ PureAct noPotency false ∧ ¬ isTrue false ∧ ¬ Nine isTrue false) ∧
  (NineLiveSomeTime inAct inAct noPotency causes () isTrue no yes yes isTrue yes onlyTrueAt ∧
    ¬ TruthCore.Latin.Aquinas.SummaTheologiae.PureActLivesReading noPotency onlyTrueAt) ∧
  (∃ g, Nine isTrue g ∧ LivesSomeTime onlyTrueAt g) ∧
  (NineLiveSomeTime inAct inAct noPotency causes () isTrue no yes yes yes yes onlyTrueAt ∧
    TruthCore.Causality.DeiFiliusLivingSelfOperation.PureActLifeAtSomeTimeIsLiving
      noPotency onlyTrueAt (TruthCore.Causality.DeiFiliusLivingSelfOperation.Control.prims isTrue) ∧
    PureAct noPotency false ∧ yes false ∧
    ¬ (TruthCore.Causality.DeiFiliusLivingSelfOperation.Control.prims isTrue).Lives false ∧
    ¬ IntellectualIsLiving yes (TruthCore.Causality.DeiFiliusLivingSelfOperation.Control.prims isTrue)) ∧
  (NineLiveSomeTime inAct inAct noPotency causes () isTrue no yes yes isTrue yes onlyTrueAt ∧
    Nine isTrue true ∧ LivesSomeTime onlyTrueAt true ∧
    ¬ (TruthCore.Causality.DeiFiliusLivingSelfOperation.Control.prims no).Lives true)

end Control
end TruthCore.Causality.DeiFiliusLivingNineScope
