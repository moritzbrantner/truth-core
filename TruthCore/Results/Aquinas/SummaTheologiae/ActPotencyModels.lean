import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.ActPotencyTheory
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3Interpretation

/-!
Finite models for the act/potency theory (#352).

Beings `a`, `b`, `c`; respects `h` (heat), `k` (another respect) and `e`
(*esse*). The **base world**: `a`, actually hot and a being, heats `b`, which is
a being and in potency to heat; `a` is simply prior to `b`; good is act; there
are no per se links. Every premise of `ActPotencyModel` holds in it. Each model
`M1`–`M8` changes the base world just enough to falsify one premise and keep
all the others; `S1` and `S2` serve the facts about the being-in-act reading.

The two-element models `NSense` … `NRegress` (beings `a`, `b`; respects `h`,
`k`) drop one premise at a time of the *prima via* from the being-in-act
reading.

The predicates are written as exhaustive, non-overlapping matches: an
overlapping catch-all pattern would make the definitions depend on `propext`.
The proofs use only case analysis, so they need no axioms.
-/

namespace TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Greek.Aristotle.Metaphysics (PotencyIsUnactualizedCapacityReading)
open TruthCore.Greek.Aristotle.Physics (BeingMovedIsActualizationOfPotencyReading)

inductive B | a | b | c
inductive R | h | k | e

/-! `b` is moved toward heat by `a` and is also actually hot: (1) fails. -/
namespace M1


def inAct : B → R → Prop :=
  fun x r => match x, r with
    | .a, .h => True | .a, .k => False | .a, .e => True
    | .b, .h => True | .b, .k => False | .b, .e => True
    | .c, .h => False | .c, .k => False | .c, .e => False

def inPotency : B → R → Prop :=
  fun x r => match x, r with
    | .a, .h => False | .a, .k => False | .a, .e => False
    | .b, .h => True | .b, .k => False | .b, .e => False
    | .c, .h => False | .c, .k => False | .c, .e => False

def movedIn : B → R → Prop :=
  fun x r => match x, r with
    | .a, .h => False | .a, .k => False | .a, .e => False
    | .b, .h => True | .b, .k => False | .b, .e => False
    | .c, .h => False | .c, .k => False | .c, .e => False

def movesIn : B → B → R → Prop :=
  fun y x r => match y, x, r with
    | .a, .a, .h => False | .a, .a, .k => False | .a, .a, .e => False
    | .a, .b, .h => True | .a, .b, .k => False | .a, .b, .e => False
    | .a, .c, .h => False | .a, .c, .k => False | .a, .c, .e => False
    | .b, .a, .h => False | .b, .a, .k => False | .b, .a, .e => False
    | .b, .b, .h => False | .b, .b, .k => False | .b, .b, .e => False
    | .b, .c, .h => False | .b, .c, .k => False | .b, .c, .e => False
    | .c, .a, .h => False | .c, .a, .k => False | .c, .a, .e => False
    | .c, .b, .h => False | .c, .b, .k => False | .c, .b, .e => False
    | .c, .c, .h => False | .c, .c, .k => False | .c, .c, .e => False

def priorSimply : B → B → Prop :=
  fun y x => match y, x with
    | .a, .a => False | .a, .b => True | .a, .c => False
    | .b, .a => False | .b, .b => False | .b, .c => False
    | .c, .a => False | .c, .b => False | .c, .c => False

def goodIn : B → R → Prop := inAct

def movesAsMoved : B → B → Prop :=
  fun y x => match y, x with
    | .a, .a => False | .a, .b => False | .a, .c => False
    | .b, .a => False | .b, .b => False | .b, .c => False
    | .c, .a => False | .c, .b => False | .c, .c => False

def model : ActPotencyModel :=
  ⟨B, R, .e, inAct, inPotency, movedIn, movesIn, priorSimply, goodIn, movesAsMoved⟩

end M1

/-! `a` is actually hot but lacks being: (2) fails. -/
namespace M2


def inAct : B → R → Prop :=
  fun x r => match x, r with
    | .a, .h => True | .a, .k => False | .a, .e => False
    | .b, .h => False | .b, .k => False | .b, .e => True
    | .c, .h => False | .c, .k => False | .c, .e => False

def inPotency : B → R → Prop :=
  fun x r => match x, r with
    | .a, .h => False | .a, .k => False | .a, .e => False
    | .b, .h => True | .b, .k => False | .b, .e => False
    | .c, .h => False | .c, .k => False | .c, .e => False

def movedIn : B → R → Prop :=
  fun x r => match x, r with
    | .a, .h => False | .a, .k => False | .a, .e => False
    | .b, .h => True | .b, .k => False | .b, .e => False
    | .c, .h => False | .c, .k => False | .c, .e => False

def movesIn : B → B → R → Prop :=
  fun y x r => match y, x, r with
    | .a, .a, .h => False | .a, .a, .k => False | .a, .a, .e => False
    | .a, .b, .h => True | .a, .b, .k => False | .a, .b, .e => False
    | .a, .c, .h => False | .a, .c, .k => False | .a, .c, .e => False
    | .b, .a, .h => False | .b, .a, .k => False | .b, .a, .e => False
    | .b, .b, .h => False | .b, .b, .k => False | .b, .b, .e => False
    | .b, .c, .h => False | .b, .c, .k => False | .b, .c, .e => False
    | .c, .a, .h => False | .c, .a, .k => False | .c, .a, .e => False
    | .c, .b, .h => False | .c, .b, .k => False | .c, .b, .e => False
    | .c, .c, .h => False | .c, .c, .k => False | .c, .c, .e => False

def priorSimply : B → B → Prop :=
  fun y x => match y, x with
    | .a, .a => False | .a, .b => True | .a, .c => False
    | .b, .a => False | .b, .b => False | .b, .c => False
    | .c, .a => False | .c, .b => False | .c, .c => False

def goodIn : B → R → Prop := inAct

def movesAsMoved : B → B → Prop :=
  fun y x => match y, x with
    | .a, .a => False | .a, .b => False | .a, .c => False
    | .b, .a => False | .b, .b => False | .b, .c => False
    | .c, .a => False | .c, .b => False | .c, .c => False

def model : ActPotencyModel :=
  ⟨B, R, .e, inAct, inPotency, movedIn, movesIn, priorSimply, goodIn, movesAsMoved⟩

end M2

/-! nothing is simply prior to anything, though `b` is in potency to heat: (3) fails. -/
namespace M3


def inAct : B → R → Prop :=
  fun x r => match x, r with
    | .a, .h => True | .a, .k => False | .a, .e => True
    | .b, .h => False | .b, .k => False | .b, .e => True
    | .c, .h => False | .c, .k => False | .c, .e => False

def inPotency : B → R → Prop :=
  fun x r => match x, r with
    | .a, .h => False | .a, .k => False | .a, .e => False
    | .b, .h => True | .b, .k => False | .b, .e => False
    | .c, .h => False | .c, .k => False | .c, .e => False

def movedIn : B → R → Prop :=
  fun x r => match x, r with
    | .a, .h => False | .a, .k => False | .a, .e => False
    | .b, .h => True | .b, .k => False | .b, .e => False
    | .c, .h => False | .c, .k => False | .c, .e => False

def movesIn : B → B → R → Prop :=
  fun y x r => match y, x, r with
    | .a, .a, .h => False | .a, .a, .k => False | .a, .a, .e => False
    | .a, .b, .h => True | .a, .b, .k => False | .a, .b, .e => False
    | .a, .c, .h => False | .a, .c, .k => False | .a, .c, .e => False
    | .b, .a, .h => False | .b, .a, .k => False | .b, .a, .e => False
    | .b, .b, .h => False | .b, .b, .k => False | .b, .b, .e => False
    | .b, .c, .h => False | .b, .c, .k => False | .b, .c, .e => False
    | .c, .a, .h => False | .c, .a, .k => False | .c, .a, .e => False
    | .c, .b, .h => False | .c, .b, .k => False | .c, .b, .e => False
    | .c, .c, .h => False | .c, .c, .k => False | .c, .c, .e => False

def priorSimply : B → B → Prop :=
  fun y x => match y, x with
    | .a, .a => False | .a, .b => False | .a, .c => False
    | .b, .a => False | .b, .b => False | .b, .c => False
    | .c, .a => False | .c, .b => False | .c, .c => False

def goodIn : B → R → Prop := inAct

def movesAsMoved : B → B → Prop :=
  fun y x => match y, x with
    | .a, .a => False | .a, .b => False | .a, .c => False
    | .b, .a => False | .b, .b => False | .b, .c => False
    | .c, .a => False | .c, .b => False | .c, .c => False

def model : ActPotencyModel :=
  ⟨B, R, .e, inAct, inPotency, movedIn, movesIn, priorSimply, goodIn, movesAsMoved⟩

end M3

/-! nothing is good, though `a` is actually hot: (4) fails. -/
namespace M4


def inAct : B → R → Prop :=
  fun x r => match x, r with
    | .a, .h => True | .a, .k => False | .a, .e => True
    | .b, .h => False | .b, .k => False | .b, .e => True
    | .c, .h => False | .c, .k => False | .c, .e => False

def inPotency : B → R → Prop :=
  fun x r => match x, r with
    | .a, .h => False | .a, .k => False | .a, .e => False
    | .b, .h => True | .b, .k => False | .b, .e => False
    | .c, .h => False | .c, .k => False | .c, .e => False

def movedIn : B → R → Prop :=
  fun x r => match x, r with
    | .a, .h => False | .a, .k => False | .a, .e => False
    | .b, .h => True | .b, .k => False | .b, .e => False
    | .c, .h => False | .c, .k => False | .c, .e => False

def movesIn : B → B → R → Prop :=
  fun y x r => match y, x, r with
    | .a, .a, .h => False | .a, .a, .k => False | .a, .a, .e => False
    | .a, .b, .h => True | .a, .b, .k => False | .a, .b, .e => False
    | .a, .c, .h => False | .a, .c, .k => False | .a, .c, .e => False
    | .b, .a, .h => False | .b, .a, .k => False | .b, .a, .e => False
    | .b, .b, .h => False | .b, .b, .k => False | .b, .b, .e => False
    | .b, .c, .h => False | .b, .c, .k => False | .b, .c, .e => False
    | .c, .a, .h => False | .c, .a, .k => False | .c, .a, .e => False
    | .c, .b, .h => False | .c, .b, .k => False | .c, .b, .e => False
    | .c, .c, .h => False | .c, .c, .k => False | .c, .c, .e => False

def priorSimply : B → B → Prop :=
  fun y x => match y, x with
    | .a, .a => False | .a, .b => True | .a, .c => False
    | .b, .a => False | .b, .b => False | .b, .c => False
    | .c, .a => False | .c, .b => False | .c, .c => False

def goodIn : B → R → Prop := fun _ _ => False

def movesAsMoved : B → B → Prop :=
  fun y x => match y, x with
    | .a, .a => False | .a, .b => False | .a, .c => False
    | .b, .a => False | .b, .b => False | .b, .c => False
    | .c, .a => False | .c, .b => False | .c, .c => False

def model : ActPotencyModel :=
  ⟨B, R, .e, inAct, inPotency, movedIn, movesIn, priorSimply, goodIn, movesAsMoved⟩

end M4

/-! `a` heats `b` without being hot; `c`, actually hot, is simply prior to `b`: (5) fails. -/
namespace M5


def inAct : B → R → Prop :=
  fun x r => match x, r with
    | .a, .h => False | .a, .k => False | .a, .e => True
    | .b, .h => False | .b, .k => False | .b, .e => True
    | .c, .h => True | .c, .k => False | .c, .e => True

def inPotency : B → R → Prop :=
  fun x r => match x, r with
    | .a, .h => False | .a, .k => False | .a, .e => False
    | .b, .h => True | .b, .k => False | .b, .e => False
    | .c, .h => False | .c, .k => False | .c, .e => False

def movedIn : B → R → Prop :=
  fun x r => match x, r with
    | .a, .h => False | .a, .k => False | .a, .e => False
    | .b, .h => True | .b, .k => False | .b, .e => False
    | .c, .h => False | .c, .k => False | .c, .e => False

def movesIn : B → B → R → Prop :=
  fun y x r => match y, x, r with
    | .a, .a, .h => False | .a, .a, .k => False | .a, .a, .e => False
    | .a, .b, .h => True | .a, .b, .k => False | .a, .b, .e => False
    | .a, .c, .h => False | .a, .c, .k => False | .a, .c, .e => False
    | .b, .a, .h => False | .b, .a, .k => False | .b, .a, .e => False
    | .b, .b, .h => False | .b, .b, .k => False | .b, .b, .e => False
    | .b, .c, .h => False | .b, .c, .k => False | .b, .c, .e => False
    | .c, .a, .h => False | .c, .a, .k => False | .c, .a, .e => False
    | .c, .b, .h => False | .c, .b, .k => False | .c, .b, .e => False
    | .c, .c, .h => False | .c, .c, .k => False | .c, .c, .e => False

def priorSimply : B → B → Prop :=
  fun y x => match y, x with
    | .a, .a => False | .a, .b => True | .a, .c => False
    | .b, .a => False | .b, .b => False | .b, .c => False
    | .c, .a => False | .c, .b => True | .c, .c => False

def goodIn : B → R → Prop := inAct

def movesAsMoved : B → B → Prop :=
  fun y x => match y, x with
    | .a, .a => False | .a, .b => False | .a, .c => False
    | .b, .a => False | .b, .b => False | .b, .c => False
    | .c, .a => False | .c, .b => False | .c, .c => False

def model : ActPotencyModel :=
  ⟨B, R, .e, inAct, inPotency, movedIn, movesIn, priorSimply, goodIn, movesAsMoved⟩

end M5

/-! `b` is being moved toward heat by nothing: (6) fails. -/
namespace M6


def inAct : B → R → Prop :=
  fun x r => match x, r with
    | .a, .h => True | .a, .k => False | .a, .e => True
    | .b, .h => False | .b, .k => False | .b, .e => True
    | .c, .h => False | .c, .k => False | .c, .e => False

def inPotency : B → R → Prop :=
  fun x r => match x, r with
    | .a, .h => False | .a, .k => False | .a, .e => False
    | .b, .h => True | .b, .k => False | .b, .e => False
    | .c, .h => False | .c, .k => False | .c, .e => False

def movedIn : B → R → Prop :=
  fun x r => match x, r with
    | .a, .h => False | .a, .k => False | .a, .e => False
    | .b, .h => True | .b, .k => False | .b, .e => False
    | .c, .h => False | .c, .k => False | .c, .e => False

def movesIn : B → B → R → Prop :=
  fun y x r => match y, x, r with
    | .a, .a, .h => False | .a, .a, .k => False | .a, .a, .e => False
    | .a, .b, .h => False | .a, .b, .k => False | .a, .b, .e => False
    | .a, .c, .h => False | .a, .c, .k => False | .a, .c, .e => False
    | .b, .a, .h => False | .b, .a, .k => False | .b, .a, .e => False
    | .b, .b, .h => False | .b, .b, .k => False | .b, .b, .e => False
    | .b, .c, .h => False | .b, .c, .k => False | .b, .c, .e => False
    | .c, .a, .h => False | .c, .a, .k => False | .c, .a, .e => False
    | .c, .b, .h => False | .c, .b, .k => False | .c, .b, .e => False
    | .c, .c, .h => False | .c, .c, .k => False | .c, .c, .e => False

def priorSimply : B → B → Prop :=
  fun y x => match y, x with
    | .a, .a => False | .a, .b => True | .a, .c => False
    | .b, .a => False | .b, .b => False | .b, .c => False
    | .c, .a => False | .c, .b => False | .c, .c => False

def goodIn : B → R → Prop := inAct

def movesAsMoved : B → B → Prop :=
  fun y x => match y, x with
    | .a, .a => False | .a, .b => False | .a, .c => False
    | .b, .a => False | .b, .b => False | .b, .c => False
    | .c, .a => False | .c, .b => False | .c, .c => False

def model : ActPotencyModel :=
  ⟨B, R, .e, inAct, inPotency, movedIn, movesIn, priorSimply, goodIn, movesAsMoved⟩

end M6

/-! `b` is moved toward heat without being in potency to it: (7) fails. -/
namespace M7


def inAct : B → R → Prop :=
  fun x r => match x, r with
    | .a, .h => True | .a, .k => False | .a, .e => True
    | .b, .h => False | .b, .k => False | .b, .e => True
    | .c, .h => False | .c, .k => False | .c, .e => False

def inPotency : B → R → Prop :=
  fun x r => match x, r with
    | .a, .h => False | .a, .k => False | .a, .e => False
    | .b, .h => False | .b, .k => False | .b, .e => False
    | .c, .h => False | .c, .k => False | .c, .e => False

def movedIn : B → R → Prop :=
  fun x r => match x, r with
    | .a, .h => False | .a, .k => False | .a, .e => False
    | .b, .h => True | .b, .k => False | .b, .e => False
    | .c, .h => False | .c, .k => False | .c, .e => False

def movesIn : B → B → R → Prop :=
  fun y x r => match y, x, r with
    | .a, .a, .h => False | .a, .a, .k => False | .a, .a, .e => False
    | .a, .b, .h => True | .a, .b, .k => False | .a, .b, .e => False
    | .a, .c, .h => False | .a, .c, .k => False | .a, .c, .e => False
    | .b, .a, .h => False | .b, .a, .k => False | .b, .a, .e => False
    | .b, .b, .h => False | .b, .b, .k => False | .b, .b, .e => False
    | .b, .c, .h => False | .b, .c, .k => False | .b, .c, .e => False
    | .c, .a, .h => False | .c, .a, .k => False | .c, .a, .e => False
    | .c, .b, .h => False | .c, .b, .k => False | .c, .b, .e => False
    | .c, .c, .h => False | .c, .c, .k => False | .c, .c, .e => False

def priorSimply : B → B → Prop :=
  fun y x => match y, x with
    | .a, .a => False | .a, .b => True | .a, .c => False
    | .b, .a => False | .b, .b => False | .b, .c => False
    | .c, .a => False | .c, .b => False | .c, .c => False

def goodIn : B → R → Prop := inAct

def movesAsMoved : B → B → Prop :=
  fun y x => match y, x with
    | .a, .a => False | .a, .b => False | .a, .c => False
    | .b, .a => False | .b, .b => False | .b, .c => False
    | .c, .a => False | .c, .b => False | .c, .c => False

def model : ActPotencyModel :=
  ⟨B, R, .e, inAct, inPotency, movedIn, movesIn, priorSimply, goodIn, movesAsMoved⟩

end M7

/-! `a` heats `b` while `c` moves `a` in respect `k`, yet `a` is no per se link: (8) fails. -/
namespace M8


def inAct : B → R → Prop :=
  fun x r => match x, r with
    | .a, .h => True | .a, .k => False | .a, .e => True
    | .b, .h => False | .b, .k => False | .b, .e => True
    | .c, .h => False | .c, .k => True | .c, .e => True

def inPotency : B → R → Prop :=
  fun x r => match x, r with
    | .a, .h => False | .a, .k => True | .a, .e => False
    | .b, .h => True | .b, .k => False | .b, .e => False
    | .c, .h => False | .c, .k => False | .c, .e => False

def movedIn : B → R → Prop :=
  fun x r => match x, r with
    | .a, .h => False | .a, .k => True | .a, .e => False
    | .b, .h => True | .b, .k => False | .b, .e => False
    | .c, .h => False | .c, .k => False | .c, .e => False

def movesIn : B → B → R → Prop :=
  fun y x r => match y, x, r with
    | .a, .a, .h => False | .a, .a, .k => False | .a, .a, .e => False
    | .a, .b, .h => True | .a, .b, .k => False | .a, .b, .e => False
    | .a, .c, .h => False | .a, .c, .k => False | .a, .c, .e => False
    | .b, .a, .h => False | .b, .a, .k => False | .b, .a, .e => False
    | .b, .b, .h => False | .b, .b, .k => False | .b, .b, .e => False
    | .b, .c, .h => False | .b, .c, .k => False | .b, .c, .e => False
    | .c, .a, .h => False | .c, .a, .k => True | .c, .a, .e => False
    | .c, .b, .h => False | .c, .b, .k => False | .c, .b, .e => False
    | .c, .c, .h => False | .c, .c, .k => False | .c, .c, .e => False

def priorSimply : B → B → Prop :=
  fun y x => match y, x with
    | .a, .a => False | .a, .b => True | .a, .c => False
    | .b, .a => False | .b, .b => False | .b, .c => False
    | .c, .a => True | .c, .b => False | .c, .c => False

def goodIn : B → R → Prop := inAct

def movesAsMoved : B → B → Prop :=
  fun y x => match y, x with
    | .a, .a => False | .a, .b => False | .a, .c => False
    | .b, .a => False | .b, .b => False | .b, .c => False
    | .c, .a => False | .c, .b => False | .c, .c => False

def model : ActPotencyModel :=
  ⟨B, R, .e, inAct, inPotency, movedIn, movesIn, priorSimply, goodIn, movesAsMoved⟩

end M8

/-! `b` is heated by `a`, actually hot, and also by `c`, which is not: every moved thing has a mover in act, but not every mover is. -/
namespace S1


def inAct : B → R → Prop :=
  fun x r => match x, r with
    | .a, .h => True | .a, .k => False | .a, .e => True
    | .b, .h => False | .b, .k => False | .b, .e => True
    | .c, .h => False | .c, .k => False | .c, .e => False

def inPotency : B → R → Prop :=
  fun x r => match x, r with
    | .a, .h => False | .a, .k => False | .a, .e => False
    | .b, .h => True | .b, .k => False | .b, .e => False
    | .c, .h => False | .c, .k => False | .c, .e => False

def movedIn : B → R → Prop :=
  fun x r => match x, r with
    | .a, .h => False | .a, .k => False | .a, .e => False
    | .b, .h => True | .b, .k => False | .b, .e => False
    | .c, .h => False | .c, .k => False | .c, .e => False

def movesIn : B → B → R → Prop :=
  fun y x r => match y, x, r with
    | .a, .a, .h => False | .a, .a, .k => False | .a, .a, .e => False
    | .a, .b, .h => True | .a, .b, .k => False | .a, .b, .e => False
    | .a, .c, .h => False | .a, .c, .k => False | .a, .c, .e => False
    | .b, .a, .h => False | .b, .a, .k => False | .b, .a, .e => False
    | .b, .b, .h => False | .b, .b, .k => False | .b, .b, .e => False
    | .b, .c, .h => False | .b, .c, .k => False | .b, .c, .e => False
    | .c, .a, .h => False | .c, .a, .k => False | .c, .a, .e => False
    | .c, .b, .h => True | .c, .b, .k => False | .c, .b, .e => False
    | .c, .c, .h => False | .c, .c, .k => False | .c, .c, .e => False

def priorSimply : B → B → Prop :=
  fun y x => match y, x with
    | .a, .a => False | .a, .b => True | .a, .c => False
    | .b, .a => False | .b, .b => False | .b, .c => False
    | .c, .a => False | .c, .b => False | .c, .c => False

def goodIn : B → R → Prop := inAct

def movesAsMoved : B → B → Prop :=
  fun y x => match y, x with
    | .a, .a => False | .a, .b => False | .a, .c => False
    | .b, .a => False | .b, .b => False | .b, .c => False
    | .c, .a => False | .c, .b => False | .c, .c => False

def model : ActPotencyModel :=
  ⟨B, R, .e, inAct, inPotency, movedIn, movesIn, priorSimply, goodIn, movesAsMoved⟩

end S1

/-! the base world plus `c`, in potency to `k`, in which nothing is in act: every prima via premise holds, but (3) fails. -/
namespace S2


def inAct : B → R → Prop :=
  fun x r => match x, r with
    | .a, .h => True | .a, .k => False | .a, .e => True
    | .b, .h => False | .b, .k => False | .b, .e => True
    | .c, .h => False | .c, .k => False | .c, .e => False

def inPotency : B → R → Prop :=
  fun x r => match x, r with
    | .a, .h => False | .a, .k => False | .a, .e => False
    | .b, .h => True | .b, .k => False | .b, .e => False
    | .c, .h => False | .c, .k => True | .c, .e => False

def movedIn : B → R → Prop :=
  fun x r => match x, r with
    | .a, .h => False | .a, .k => False | .a, .e => False
    | .b, .h => True | .b, .k => False | .b, .e => False
    | .c, .h => False | .c, .k => False | .c, .e => False

def movesIn : B → B → R → Prop :=
  fun y x r => match y, x, r with
    | .a, .a, .h => False | .a, .a, .k => False | .a, .a, .e => False
    | .a, .b, .h => True | .a, .b, .k => False | .a, .b, .e => False
    | .a, .c, .h => False | .a, .c, .k => False | .a, .c, .e => False
    | .b, .a, .h => False | .b, .a, .k => False | .b, .a, .e => False
    | .b, .b, .h => False | .b, .b, .k => False | .b, .b, .e => False
    | .b, .c, .h => False | .b, .c, .k => False | .b, .c, .e => False
    | .c, .a, .h => False | .c, .a, .k => False | .c, .a, .e => False
    | .c, .b, .h => False | .c, .b, .k => False | .c, .b, .e => False
    | .c, .c, .h => False | .c, .c, .k => False | .c, .c, .e => False

def priorSimply : B → B → Prop :=
  fun y x => match y, x with
    | .a, .a => False | .a, .b => True | .a, .c => False
    | .b, .a => False | .b, .b => False | .b, .c => False
    | .c, .a => False | .c, .b => False | .c, .c => False

def goodIn : B → R → Prop := inAct

def movesAsMoved : B → B → Prop :=
  fun y x => match y, x with
    | .a, .a => False | .a, .b => False | .a, .c => False
    | .b, .a => False | .b, .b => False | .b, .c => False
    | .c, .a => False | .c, .b => False | .c, .c => False

def model : ActPotencyModel :=
  ⟨B, R, .e, inAct, inPotency, movedIn, movesIn, priorSimply, goodIn, movesAsMoved⟩

end S2

/-- Each act/potency premise fails in a model of all the others. -/
theorem premisesIndependent : ActPotencyPremisesIndependent := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (1) fails in `M1`
    intro hAll
    have hT := hAll M1.model
      (by exact Exists.intro B.b (Exists.intro R.h trivial))
      (by intro x; constructor; intro y h; cases y <;> cases x <;> exact False.elim h)
      (by intro x r h; cases x <;> cases r <;> first | exact trivial | exact False.elim h)
      (by intro x r h; cases x <;> cases r <;> first | exact False.elim h | exact ⟨B.a, trivial, trivial⟩ | exact ⟨B.b, trivial, trivial⟩ | exact ⟨B.c, trivial, trivial⟩)
      (by intro x r; exact Iff.rfl)
      (by intro y x r h; cases y <;> cases x <;> cases r <;> first | exact trivial | exact False.elim h)
      (by intro x r h; cases x <;> cases r <;> first | exact False.elim h | exact ⟨B.a, trivial⟩ | exact ⟨B.b, trivial⟩ | exact ⟨B.c, trivial⟩)
      (by intro x r h; cases x <;> cases r <;> first | exact trivial | exact False.elim h)
      (by intro y x r hne hm hmv; obtain ⟨r', hm'⟩ := hmv; cases y <;> cases x <;> cases r <;> cases r' <;> first | exact False.elim hm | exact False.elim hm' | exact absurd rfl hne | exact trivial)
    exact hT B.b R.h ⟨trivial, trivial⟩
  · -- (2) fails in `M2`
    intro hAll
    have hT := hAll M2.model
      (by exact Exists.intro B.b (Exists.intro R.h trivial))
      (by intro x; constructor; intro y h; cases y <;> cases x <;> exact False.elim h)
      (by intro x r h; cases x <;> cases r <;> first | exact False.elim h.1 | exact False.elim h.2)
      (by intro x r h; cases x <;> cases r <;> first | exact False.elim h | exact ⟨B.a, trivial, trivial⟩ | exact ⟨B.b, trivial, trivial⟩ | exact ⟨B.c, trivial, trivial⟩)
      (by intro x r; exact Iff.rfl)
      (by intro y x r h; cases y <;> cases x <;> cases r <;> first | exact trivial | exact False.elim h)
      (by intro x r h; cases x <;> cases r <;> first | exact False.elim h | exact ⟨B.a, trivial⟩ | exact ⟨B.b, trivial⟩ | exact ⟨B.c, trivial⟩)
      (by intro x r h; cases x <;> cases r <;> first | exact trivial | exact False.elim h)
      (by intro y x r hne hm hmv; obtain ⟨r', hm'⟩ := hmv; cases y <;> cases x <;> cases r <;> cases r' <;> first | exact False.elim hm | exact False.elim hm' | exact absurd rfl hne | exact trivial)
    exact hT B.a R.h trivial
  · -- (3) fails in `M3`
    intro hAll
    have hT := hAll M3.model
      (by exact Exists.intro B.b (Exists.intro R.h trivial))
      (by intro x; constructor; intro y h; cases y <;> cases x <;> exact False.elim h)
      (by intro x r h; cases x <;> cases r <;> first | exact False.elim h.1 | exact False.elim h.2)
      (by intro x r h; cases x <;> cases r <;> first | exact trivial | exact False.elim h)
      (by intro x r; exact Iff.rfl)
      (by intro y x r h; cases y <;> cases x <;> cases r <;> first | exact trivial | exact False.elim h)
      (by intro x r h; cases x <;> cases r <;> first | exact False.elim h | exact ⟨B.a, trivial⟩ | exact ⟨B.b, trivial⟩ | exact ⟨B.c, trivial⟩)
      (by intro x r h; cases x <;> cases r <;> first | exact trivial | exact False.elim h)
      (by intro y x r hne hm hmv; obtain ⟨r', hm'⟩ := hmv; cases y <;> cases x <;> cases r <;> cases r' <;> first | exact False.elim hm | exact False.elim hm' | exact absurd rfl hne | exact trivial)
    obtain ⟨y, hy, hp⟩ := hT B.b R.h trivial; cases y <;> first | exact False.elim hy | exact False.elim hp
  · -- (4) fails in `M4`
    intro hAll
    have hT := hAll M4.model
      (by exact Exists.intro B.b (Exists.intro R.h trivial))
      (by intro x; constructor; intro y h; cases y <;> cases x <;> exact False.elim h)
      (by intro x r h; cases x <;> cases r <;> first | exact False.elim h.1 | exact False.elim h.2)
      (by intro x r h; cases x <;> cases r <;> first | exact trivial | exact False.elim h)
      (by intro x r h; cases x <;> cases r <;> first | exact False.elim h | exact ⟨B.a, trivial, trivial⟩ | exact ⟨B.b, trivial, trivial⟩ | exact ⟨B.c, trivial, trivial⟩)
      (by intro y x r h; cases y <;> cases x <;> cases r <;> first | exact trivial | exact False.elim h)
      (by intro x r h; cases x <;> cases r <;> first | exact False.elim h | exact ⟨B.a, trivial⟩ | exact ⟨B.b, trivial⟩ | exact ⟨B.c, trivial⟩)
      (by intro x r h; cases x <;> cases r <;> first | exact trivial | exact False.elim h)
      (by intro y x r hne hm hmv; obtain ⟨r', hm'⟩ := hmv; cases y <;> cases x <;> cases r <;> cases r' <;> first | exact False.elim hm | exact False.elim hm' | exact absurd rfl hne | exact trivial)
    exact (hT B.a R.h).mpr trivial
  · -- (5) fails in `M5`
    intro hAll
    have hT := hAll M5.model
      (by exact Exists.intro B.b (Exists.intro R.h trivial))
      (by intro x; constructor; intro y h; cases y <;> cases x <;> exact False.elim h)
      (by intro x r h; cases x <;> cases r <;> first | exact False.elim h.1 | exact False.elim h.2)
      (by intro x r h; cases x <;> cases r <;> first | exact trivial | exact False.elim h)
      (by intro x r h; cases x <;> cases r <;> first | exact False.elim h | exact ⟨B.a, trivial, trivial⟩ | exact ⟨B.b, trivial, trivial⟩ | exact ⟨B.c, trivial, trivial⟩)
      (by intro x r; exact Iff.rfl)
      (by intro x r h; cases x <;> cases r <;> first | exact False.elim h | exact ⟨B.a, trivial⟩ | exact ⟨B.b, trivial⟩ | exact ⟨B.c, trivial⟩)
      (by intro x r h; cases x <;> cases r <;> first | exact trivial | exact False.elim h)
      (by intro y x r hne hm hmv; obtain ⟨r', hm'⟩ := hmv; cases y <;> cases x <;> cases r <;> cases r' <;> first | exact False.elim hm | exact False.elim hm' | exact absurd rfl hne | exact trivial)
    exact hT B.a B.b R.h trivial
  · -- (6) fails in `M6`
    intro hAll
    have hT := hAll M6.model
      (by exact Exists.intro B.b (Exists.intro R.h trivial))
      (by intro x; constructor; intro y h; cases y <;> cases x <;> exact False.elim h)
      (by intro x r h; cases x <;> cases r <;> first | exact False.elim h.1 | exact False.elim h.2)
      (by intro x r h; cases x <;> cases r <;> first | exact trivial | exact False.elim h)
      (by intro x r h; cases x <;> cases r <;> first | exact False.elim h | exact ⟨B.a, trivial, trivial⟩ | exact ⟨B.b, trivial, trivial⟩ | exact ⟨B.c, trivial, trivial⟩)
      (by intro x r; exact Iff.rfl)
      (by intro y x r h; cases y <;> cases x <;> cases r <;> first | exact trivial | exact False.elim h)
      (by intro x r h; cases x <;> cases r <;> first | exact trivial | exact False.elim h)
      (by intro y x r hne hm hmv; obtain ⟨r', hm'⟩ := hmv; cases y <;> cases x <;> cases r <;> cases r' <;> first | exact False.elim hm | exact False.elim hm' | exact absurd rfl hne | exact trivial)
    obtain ⟨y, hy⟩ := hT B.b R.h trivial; cases y <;> exact False.elim hy
  · -- (7) fails in `M7`
    intro hAll
    have hT := hAll M7.model
      (by exact Exists.intro B.b (Exists.intro R.h trivial))
      (by intro x; constructor; intro y h; cases y <;> cases x <;> exact False.elim h)
      (by intro x r h; cases x <;> cases r <;> first | exact False.elim h.1 | exact False.elim h.2)
      (by intro x r h; cases x <;> cases r <;> first | exact trivial | exact False.elim h)
      (by intro x r h; cases x <;> cases r <;> first | exact False.elim h | exact ⟨B.a, trivial, trivial⟩ | exact ⟨B.b, trivial, trivial⟩ | exact ⟨B.c, trivial, trivial⟩)
      (by intro x r; exact Iff.rfl)
      (by intro y x r h; cases y <;> cases x <;> cases r <;> first | exact trivial | exact False.elim h)
      (by intro x r h; cases x <;> cases r <;> first | exact False.elim h | exact ⟨B.a, trivial⟩ | exact ⟨B.b, trivial⟩ | exact ⟨B.c, trivial⟩)
      (by intro y x r hne hm hmv; obtain ⟨r', hm'⟩ := hmv; cases y <;> cases x <;> cases r <;> cases r' <;> first | exact False.elim hm | exact False.elim hm' | exact absurd rfl hne | exact trivial)
    exact hT B.b R.h trivial
  · -- (8) fails in `M8`
    intro hAll
    have hT := hAll M8.model
      (by exact Exists.intro B.b (Exists.intro R.h trivial))
      (by intro x; constructor; intro y h; cases y <;> cases x <;> exact False.elim h)
      (by intro x r h; cases x <;> cases r <;> first | exact False.elim h.1 | exact False.elim h.2)
      (by intro x r h; cases x <;> cases r <;> first | exact trivial | exact False.elim h)
      (by intro x r h; cases x <;> cases r <;> first | exact False.elim h | exact ⟨B.a, trivial, trivial⟩ | exact ⟨B.b, trivial, trivial⟩ | exact ⟨B.c, trivial, trivial⟩)
      (by intro x r; exact Iff.rfl)
      (by intro y x r h; cases y <;> cases x <;> cases r <;> first | exact trivial | exact False.elim h)
      (by intro x r h; cases x <;> cases r <;> first | exact False.elim h | exact ⟨B.a, trivial⟩ | exact ⟨B.b, trivial⟩ | exact ⟨B.c, trivial⟩)
      (by intro x r h; cases x <;> cases r <;> first | exact trivial | exact False.elim h)
    exact hT B.a B.b R.h (fun h => nomatch h) trivial ⟨R.k, trivial⟩

/-- The definitional analyses of potency (Θ.6) and of being moved (Physics
III.1) entail premises (1) and (7) and are conservative over them. -/
theorem definitionalAnalysesConservative : ActPotencyDefinitionalAnalysesConservative := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro Being Respect InAct InPotency CanBe hDef x r h
    exact (hDef x r |>.mp h.2).2 h.1
  · intro Being Respect InAct InPotency hNotBoth
    exact ⟨InPotency, fun x r =>
      ⟨fun h => ⟨h, fun ha => hNotBoth x r ⟨ha, h⟩⟩, fun h => h.1⟩⟩
  · intro Being Respect MovedIn InPotency ActualizedQuaPotential hDef x r h
    exact (hDef x r |>.mp h).1
  · intro Being Respect MovedIn InPotency hPotency
    exact ⟨MovedIn, fun x r =>
      ⟨fun h => ⟨hPotency x r h, h⟩, fun h => h.2⟩⟩

/-- Facts about the being-in-act reading of *nisi per aliquod ens in actu*. -/
theorem beingInActReadingFacts : BeingInActReadingFacts := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro Being Respect MovedIn MovesIn InAct hMover hAct x r h
    obtain ⟨y, hy⟩ := hMover x r h
    exact ⟨y, hy, hAct y x r hy⟩
  · intro Being Respect MovedIn MovesIn InAct hS x r h
    obtain ⟨y, hy, _⟩ := hS x r h
    exact ⟨y, hy⟩
  · intro hAll
    have hT := hAll B R S1.movedIn S1.movesIn S1.inAct
      (by intro x r h; cases x <;> cases r <;> first | exact False.elim h | exact ⟨B.a, trivial, trivial⟩)
    exact hT B.c B.b R.h trivial
  · -- (3) fails in `S2`
    intro hAll
    have hT := hAll S2.model
      (by exact Exists.intro B.b (Exists.intro R.h trivial))
      (by intro x; constructor; intro y h; cases y <;> cases x <;> exact False.elim h)
      (by intro x r h; cases x <;> cases r <;> first | exact False.elim h.1 | exact False.elim h.2)
      (by intro y x r h; cases y <;> cases x <;> cases r <;> first | exact trivial | exact False.elim h)
      (by intro x r h; cases x <;> cases r <;> first | exact False.elim h | exact ⟨B.a, trivial⟩ | exact ⟨B.b, trivial⟩ | exact ⟨B.c, trivial⟩)
      (by intro x r h; cases x <;> cases r <;> first | exact trivial | exact False.elim h)
      (by intro y x r hne hm hmv; obtain ⟨r', hm'⟩ := hmv; cases y <;> cases x <;> cases r <;> cases r' <;> first | exact False.elim hm | exact False.elim hm' | exact absurd rfl hne | exact trivial)
      (by intro x r h; cases x <;> cases r <;> first | exact False.elim h | exact ⟨B.a, trivial, trivial⟩ | exact ⟨B.b, trivial, trivial⟩ | exact ⟨B.c, trivial, trivial⟩)
    obtain ⟨y, hy, _⟩ := hT B.c R.k trivial; cases y <;> exact False.elim hy

/-! ### Omission countermodels for the *prima via* from the being-in-act reading -/

inductive B2 | a | b
inductive R2 | h | k

/-! nothing is moved and nothing moves. -/
namespace NSense


def movedIn : B2 → R2 → Prop :=
  fun x r => match x, r with
    | .a, .h => False | .a, .k => False
    | .b, .h => False | .b, .k => False

def movesIn : B2 → B2 → R2 → Prop :=
  fun y x r => match y, x, r with
    | .a, .a, .h => False | .a, .a, .k => False
    | .a, .b, .h => False | .a, .b, .k => False
    | .b, .a, .h => False | .b, .a, .k => False
    | .b, .b, .h => False | .b, .b, .k => False

def inPotency : B2 → R2 → Prop :=
  fun x r => match x, r with
    | .a, .h => False | .a, .k => False
    | .b, .h => False | .b, .k => False

def inAct : B2 → R2 → Prop :=
  fun x r => match x, r with
    | .a, .h => False | .a, .k => False
    | .b, .h => False | .b, .k => False

def movesAsMoved : B2 → B2 → Prop :=
  fun y x => match y, x with
    | .a, .a => False | .a, .b => False
    | .b, .a => False | .b, .b => False

def model : MotionModel :=
  ⟨B2, R2, movedIn, movesIn, inPotency, inAct, movesAsMoved, fun _ _ _ _ => False⟩

end NSense

/-! `a` heats itself, being actually hot and in potency to nothing. -/
namespace NPotency


def movedIn : B2 → R2 → Prop :=
  fun x r => match x, r with
    | .a, .h => True | .a, .k => False
    | .b, .h => False | .b, .k => False

def movesIn : B2 → B2 → R2 → Prop :=
  fun y x r => match y, x, r with
    | .a, .a, .h => True | .a, .a, .k => False
    | .a, .b, .h => False | .a, .b, .k => False
    | .b, .a, .h => False | .b, .a, .k => False
    | .b, .b, .h => False | .b, .b, .k => False

def inPotency : B2 → R2 → Prop :=
  fun x r => match x, r with
    | .a, .h => False | .a, .k => False
    | .b, .h => False | .b, .k => False

def inAct : B2 → R2 → Prop :=
  fun x r => match x, r with
    | .a, .h => True | .a, .k => False
    | .b, .h => False | .b, .k => False

def movesAsMoved : B2 → B2 → Prop :=
  fun y x => match y, x with
    | .a, .a => False | .a, .b => False
    | .b, .a => False | .b, .b => False

def model : MotionModel :=
  ⟨B2, R2, movedIn, movesIn, inPotency, inAct, movesAsMoved, fun _ _ _ _ => False⟩

end NPotency

/-! `a` is being heated by nothing. -/
namespace NReduction


def movedIn : B2 → R2 → Prop :=
  fun x r => match x, r with
    | .a, .h => True | .a, .k => False
    | .b, .h => False | .b, .k => False

def movesIn : B2 → B2 → R2 → Prop :=
  fun y x r => match y, x, r with
    | .a, .a, .h => False | .a, .a, .k => False
    | .a, .b, .h => False | .a, .b, .k => False
    | .b, .a, .h => False | .b, .a, .k => False
    | .b, .b, .h => False | .b, .b, .k => False

def inPotency : B2 → R2 → Prop :=
  fun x r => match x, r with
    | .a, .h => True | .a, .k => False
    | .b, .h => False | .b, .k => False

def inAct : B2 → R2 → Prop :=
  fun x r => match x, r with
    | .a, .h => False | .a, .k => False
    | .b, .h => False | .b, .k => False

def movesAsMoved : B2 → B2 → Prop :=
  fun y x => match y, x with
    | .a, .a => False | .a, .b => False
    | .b, .a => False | .b, .b => False

def model : MotionModel :=
  ⟨B2, R2, movedIn, movesIn, inPotency, inAct, movesAsMoved, fun _ _ _ _ => False⟩

end NReduction

/-! `a` heats itself, being at once actually and potentially hot. -/
namespace NNotBoth


def movedIn : B2 → R2 → Prop :=
  fun x r => match x, r with
    | .a, .h => True | .a, .k => False
    | .b, .h => False | .b, .k => False

def movesIn : B2 → B2 → R2 → Prop :=
  fun y x r => match y, x, r with
    | .a, .a, .h => True | .a, .a, .k => False
    | .a, .b, .h => False | .a, .b, .k => False
    | .b, .a, .h => False | .b, .a, .k => False
    | .b, .b, .h => False | .b, .b, .k => False

def inPotency : B2 → R2 → Prop :=
  fun x r => match x, r with
    | .a, .h => True | .a, .k => False
    | .b, .h => False | .b, .k => False

def inAct : B2 → R2 → Prop :=
  fun x r => match x, r with
    | .a, .h => True | .a, .k => False
    | .b, .h => False | .b, .k => False

def movesAsMoved : B2 → B2 → Prop :=
  fun y x => match y, x with
    | .a, .a => False | .a, .b => False
    | .b, .a => False | .b, .b => False

def model : MotionModel :=
  ⟨B2, R2, movedIn, movesIn, inPotency, inAct, movesAsMoved, fun _ _ _ _ => False⟩

end NNotBoth

/-! `b` heats `a` while `a` moves `b` in `k`; neither is a per se link. -/
namespace NPerSe


def movedIn : B2 → R2 → Prop :=
  fun x r => match x, r with
    | .a, .h => True | .a, .k => False
    | .b, .h => False | .b, .k => True

def movesIn : B2 → B2 → R2 → Prop :=
  fun y x r => match y, x, r with
    | .a, .a, .h => False | .a, .a, .k => False
    | .a, .b, .h => False | .a, .b, .k => True
    | .b, .a, .h => True | .b, .a, .k => False
    | .b, .b, .h => False | .b, .b, .k => False

def inPotency : B2 → R2 → Prop :=
  fun x r => match x, r with
    | .a, .h => True | .a, .k => False
    | .b, .h => False | .b, .k => True

def inAct : B2 → R2 → Prop :=
  fun x r => match x, r with
    | .a, .h => False | .a, .k => True
    | .b, .h => True | .b, .k => False

def movesAsMoved : B2 → B2 → Prop :=
  fun y x => match y, x with
    | .a, .a => False | .a, .b => False
    | .b, .a => False | .b, .b => False

def model : MotionModel :=
  ⟨B2, R2, movedIn, movesIn, inPotency, inAct, movesAsMoved, fun _ _ _ _ => False⟩

end NPerSe

/-! as `NPerSe`, but each is a per se link of the other: a per se series without a first. -/
namespace NRegress


def movedIn : B2 → R2 → Prop :=
  fun x r => match x, r with
    | .a, .h => True | .a, .k => False
    | .b, .h => False | .b, .k => True

def movesIn : B2 → B2 → R2 → Prop :=
  fun y x r => match y, x, r with
    | .a, .a, .h => False | .a, .a, .k => False
    | .a, .b, .h => False | .a, .b, .k => True
    | .b, .a, .h => True | .b, .a, .k => False
    | .b, .b, .h => False | .b, .b, .k => False

def inPotency : B2 → R2 → Prop :=
  fun x r => match x, r with
    | .a, .h => True | .a, .k => False
    | .b, .h => False | .b, .k => True

def inAct : B2 → R2 → Prop :=
  fun x r => match x, r with
    | .a, .h => False | .a, .k => True
    | .b, .h => True | .b, .k => False

def movesAsMoved : B2 → B2 → Prop :=
  fun y x => match y, x with
    | .a, .a => False | .a, .b => True
    | .b, .a => True | .b, .b => False

def model : MotionModel :=
  ⟨B2, R2, movedIn, movesIn, inPotency, inAct, movesAsMoved, fun _ _ _ _ => False⟩

end NRegress

/-- Each premise of `PrimaViaFromBeingInAct.primaViaFromBeingInAct` is needed:
dropping any one of them leaves a model of the rest with no mover moved by
none. -/
theorem primaViaFromBeingInActPremisesNeeded : PrimaViaFromBeingInActPremisesNeeded := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- without the sense premise: `NSense`
    intro hAll
    have hC := hAll NSense.model
      (by intro x r h; cases x <;> cases r <;> first | exact trivial | exact False.elim h)
      (by intro x r h; cases x <;> cases r <;> first | exact False.elim h | exact ⟨B2.a, trivial, trivial⟩ | exact ⟨B2.b, trivial, trivial⟩)
      (by intro x r h; cases x <;> cases r <;> first | exact False.elim h.1 | exact False.elim h.2)
      (by intro y x r hne hm hmv; obtain ⟨r', hm'⟩ := hmv; cases y <;> cases x <;> cases r <;> cases r' <;> first | exact False.elim hm | exact False.elim hm' | exact absurd rfl hne | exact trivial)
      (by intro x; constructor; intro y h; cases y <;> cases x <;> exact False.elim h)
    apply hC; intro ⟨f, ⟨x, r, hm⟩, hun⟩; cases f <;> cases x <;> cases r <;> first | exact False.elim hm | exact hun R2.h trivial | exact hun R2.k trivial
  · -- without the potency premise: `NPotency`
    intro hAll
    have hC := hAll NPotency.model
      (by exact Exists.intro B2.a (Exists.intro R2.h trivial))
      (by intro x r h; cases x <;> cases r <;> first | exact False.elim h | exact ⟨B2.a, trivial, trivial⟩ | exact ⟨B2.b, trivial, trivial⟩)
      (by intro x r h; cases x <;> cases r <;> first | exact False.elim h.1 | exact False.elim h.2)
      (by intro y x r hne hm hmv; obtain ⟨r', hm'⟩ := hmv; cases y <;> cases x <;> cases r <;> cases r' <;> first | exact False.elim hm | exact False.elim hm' | exact absurd rfl hne | exact trivial)
      (by intro x; constructor; intro y h; cases y <;> cases x <;> exact False.elim h)
    apply hC; intro ⟨f, ⟨x, r, hm⟩, hun⟩; cases f <;> cases x <;> cases r <;> first | exact False.elim hm | exact hun R2.h trivial | exact hun R2.k trivial
  · -- without the reduction premise: `NReduction`
    intro hAll
    have hC := hAll NReduction.model
      (by exact Exists.intro B2.a (Exists.intro R2.h trivial))
      (by intro x r h; cases x <;> cases r <;> first | exact trivial | exact False.elim h)
      (by intro x r h; cases x <;> cases r <;> first | exact False.elim h.1 | exact False.elim h.2)
      (by intro y x r hne hm hmv; obtain ⟨r', hm'⟩ := hmv; cases y <;> cases x <;> cases r <;> cases r' <;> first | exact False.elim hm | exact False.elim hm' | exact absurd rfl hne | exact trivial)
      (by intro x; constructor; intro y h; cases y <;> cases x <;> exact False.elim h)
    apply hC; intro ⟨f, ⟨x, r, hm⟩, hun⟩; cases f <;> cases x <;> cases r <;> first | exact False.elim hm | exact hun R2.h trivial | exact hun R2.k trivial
  · -- without the notboth premise: `NNotBoth`
    intro hAll
    have hC := hAll NNotBoth.model
      (by exact Exists.intro B2.a (Exists.intro R2.h trivial))
      (by intro x r h; cases x <;> cases r <;> first | exact trivial | exact False.elim h)
      (by intro x r h; cases x <;> cases r <;> first | exact False.elim h | exact ⟨B2.a, trivial, trivial⟩ | exact ⟨B2.b, trivial, trivial⟩)
      (by intro y x r hne hm hmv; obtain ⟨r', hm'⟩ := hmv; cases y <;> cases x <;> cases r <;> cases r' <;> first | exact False.elim hm | exact False.elim hm' | exact absurd rfl hne | exact trivial)
      (by intro x; constructor; intro y h; cases y <;> cases x <;> exact False.elim h)
    apply hC; intro ⟨f, ⟨x, r, hm⟩, hun⟩; cases f <;> cases x <;> cases r <;> first | exact False.elim hm | exact hun R2.h trivial | exact hun R2.k trivial
  · -- without the perse premise: `NPerSe`
    intro hAll
    have hC := hAll NPerSe.model
      (by exact Exists.intro B2.a (Exists.intro R2.h trivial))
      (by intro x r h; cases x <;> cases r <;> first | exact trivial | exact False.elim h)
      (by intro x r h; cases x <;> cases r <;> first | exact False.elim h | exact ⟨B2.a, trivial, trivial⟩ | exact ⟨B2.b, trivial, trivial⟩)
      (by intro x r h; cases x <;> cases r <;> first | exact False.elim h.1 | exact False.elim h.2)
      (by intro x; constructor; intro y h; cases y <;> cases x <;> exact False.elim h)
    apply hC; intro ⟨f, ⟨x, r, hm⟩, hun⟩; cases f <;> cases x <;> cases r <;> first | exact False.elim hm | exact hun R2.h trivial | exact hun R2.k trivial
  · -- without the regress premise: `NRegress`
    intro hAll
    have hC := hAll NRegress.model
      (by exact Exists.intro B2.a (Exists.intro R2.h trivial))
      (by intro x r h; cases x <;> cases r <;> first | exact trivial | exact False.elim h)
      (by intro x r h; cases x <;> cases r <;> first | exact False.elim h | exact ⟨B2.a, trivial, trivial⟩ | exact ⟨B2.b, trivial, trivial⟩)
      (by intro x r h; cases x <;> cases r <;> first | exact False.elim h.1 | exact False.elim h.2)
      (by intro y x r hne hm hmv; obtain ⟨r', hm'⟩ := hmv; cases y <;> cases x <;> cases r <;> cases r' <;> first | exact False.elim hm | exact False.elim hm' | exact absurd rfl hne | exact trivial)
    apply hC; intro ⟨f, ⟨x, r, hm⟩, hun⟩; cases f <;> cases x <;> cases r <;> first | exact False.elim hm | exact hun R2.h trivial | exact hun R2.k trivial

end TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels
