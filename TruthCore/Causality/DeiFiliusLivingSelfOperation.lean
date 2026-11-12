module

public import TruthCore.Causality.DeiFiliusAttributeField
public import TruthCore.Causality.SelfOperationLife

/-! *Vivus* at the spine's root through the self-operation route

`DeiFiliusAttributeField` gives the living conjunct of `DeiFiliusAttributes`
(LIVING_1, the timeless primitive `Primitives.Lives`) at the spine's root only
through the open bridge `IntellectualIsLiving` (whatever has intellect lives).
The corpus already derives a time-indexed life for pure act:
`STMT-PURE-ACT-LIVES` (`PureActLivesReading`: whatever is in potency in no
respect lives at some time of the duration frame, LIVING_2), result
`PURE-ACT-LIVES-FROM-SELF-OPERATION` (life as self-operation, q.18 a.3 co., from
three open premises). The root is pure act: its `immutable` conjunct is
`IsImmutable InPotency`, whose body is `PureAct InPotency`.

The two senses are not identified (invariant 7; disambiguation `1f2d3b9b`). The
passage from LIVING_2 to LIVING_1 is one explicit, open sense bridge, restricted
to pure act: `PureActLifeAtSomeTimeIsLiving`. The restriction is what makes it
a modest bridge. For a being that is in potency in some respect, life present
at one time need not be its life without a time index (it may begin or cease).
For a being in potency in no respect, the open premise
`STMT-LIFE-BOUNDARY-REQUIRES-POTENCY` (whatever begins or ceases to live is in
potency in itself; q.10 a.1 co. supports only the weaker "is not altogether
immutable", and q.9 a.1 does not cover beginning or ceasing to live) would make
its life at some time not a temporary episode. That motivation covers only the
step from some time to every time of the frame; the further step from life at
every time to the timeless LIVING_1 (sempiternal versus eternal, #979) is not
motivated by it and is carried by the bridge alone. `Primitives.Lives` stays
primitive. `LivesSomeTime` is a reducible definition, so LIVING_2 is
distinguished from a raw `∃ t, LivesAt g t` only nominally. The unrestricted
version `LifeAtSomeTimeIsLiving` is recorded for comparison and is not used.

Analyst formulations, attribution deferred. -/

@[expose] public section

namespace TruthCore.Causality.DeiFiliusLivingSelfOperation

open TruthCore.Latin.Aquinas.SummaTheologiae (PureAct PureActLivesReading)
open TruthCore.Causality.DeiFiliusAttributeField

/-- Open sense bridge LIVING_2 → LIVING_1, restricted to pure act: whatever is in
potency in no respect and lives at some time of the duration frame lives
(timeless `Primitives.Lives`). Partly motivated by the open premise
`STMT-LIFE-BOUNDARY-REQUIRES-POTENCY` (no beginning or end of life without
potency), which covers only some time to every time; not derived. -/
def PureActLifeAtSomeTimeIsLiving {Being Respect Time : Type}
    (InPotency : Being → Respect → Prop) (LivesAt : Being → Time → Prop)
    (D : Primitives Being) : Prop :=
  ∀ g, PureAct InPotency g → LivesSomeTime LivesAt g → D.Lives g

/-- The unrestricted sense bridge, for comparison only (not used by any
argument): whatever lives at some time of the frame lives timelessly. It is
strictly stronger than `PureActLifeAtSomeTimeIsLiving` (`Control.Controls`
part 4); a being that lived once and is in potency is the case where the two
come apart. -/
def LifeAtSomeTimeIsLiving {Being Time : Type} (LivesAt : Being → Time → Prop)
    (D : Primitives Being) : Prop :=
  ∀ g, LivesSomeTime LivesAt g → D.Lives g

namespace Control

/-- Primitives on `Bool` with only `Lives` varying. -/
def prims (L : Bool → Prop) : Primitives Bool :=
  ⟨L, fun _ => True, fun _ => True, fun _ => True, fun _ => True⟩

def noPotency (_ : Bool) (_ : Unit) : Prop := False
def allPotency (_ : Bool) (_ : Unit) : Prop := True
def livesAlways (_ : Bool) (_ : Unit) : Prop := True
def livesNever (_ : Bool) (_ : Unit) : Prop := False

/-- Five interpretations on two beings (`Bool`), one respect and one time, and
one general fact:

1. nonvacuity: no potency, life at every time, every being LIVING_1; both the
   time-indexed premise and the sense bridge hold, and a pure act lives;
2. sense-mixing control: no potency, life at every time, nothing LIVING_1; the
   time-indexed premise holds, the bridge fails, and a pure act lives at some
   time (LIVING_2) without living (LIVING_1);
3. no potency, no life at any time, nothing LIVING_1; the bridge holds
   (vacuously), the time-indexed premise fails, and a pure act does not live;
4. everything in potency, life at every time, nothing LIVING_1; the restricted
   bridge holds and the unrestricted one fails;
5. `false` alone in potency, life at every time, only `true` LIVING_1, both
   intellectual; the restricted bridge and the time-indexed premise hold while
   `IntellectualIsLiving` fails, so the new route does not presuppose the old
   bridge;
6. in general, the unrestricted bridge implies the restricted one (with 4,
   the restricted bridge is strictly weaker). -/
def Controls : Prop :=
  (PureActLivesReading noPotency livesAlways ∧
    PureActLifeAtSomeTimeIsLiving noPotency livesAlways (prims fun _ => True) ∧
    ∃ g, PureAct noPotency g ∧ (prims fun _ => True).Lives g) ∧
  (PureActLivesReading noPotency livesAlways ∧
    ¬ PureActLifeAtSomeTimeIsLiving noPotency livesAlways (prims fun _ => False) ∧
    ∃ g, PureAct noPotency g ∧ LivesSomeTime livesAlways g ∧
      ¬ (prims fun _ => False).Lives g) ∧
  (¬ PureActLivesReading noPotency livesNever ∧
    PureActLifeAtSomeTimeIsLiving noPotency livesNever (prims fun _ => False) ∧
    ∃ g, PureAct noPotency g ∧ ¬ (prims fun _ => False).Lives g) ∧
  (PureActLifeAtSomeTimeIsLiving allPotency livesAlways (prims fun _ => False) ∧
    ¬ LifeAtSomeTimeIsLiving livesAlways (prims fun _ => False)) ∧
  (PureActLivesReading (fun g (_ : Unit) => g = false) livesAlways ∧
    PureActLifeAtSomeTimeIsLiving (fun g (_ : Unit) => g = false) livesAlways
      (prims fun g => g = true) ∧
    ¬ IntellectualIsLiving (fun _ => True) (prims fun g => g = true)) ∧
  (∀ (Being Respect Time : Type) (InPotency : Being → Respect → Prop)
      (LivesAt : Being → Time → Prop) (D : Primitives Being),
    LifeAtSomeTimeIsLiving LivesAt D → PureActLifeAtSomeTimeIsLiving InPotency LivesAt D)

end Control
end TruthCore.Causality.DeiFiliusLivingSelfOperation
