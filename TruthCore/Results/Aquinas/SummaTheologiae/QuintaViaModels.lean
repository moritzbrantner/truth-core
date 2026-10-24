/-!
Finite models for the *quinta via* (ST I q.2 a.3, fifth way; #148).

Two natural bodies `b0`, `b1` and two possible directors `d0`, `d1`; one end
and one respect (`Unit`). The predicates are written as non-overlapping matches,
so the models need no axioms.
-/

namespace TruthCore.Results.Aquinas.SummaTheologiae.QuintaViaModels

inductive W | b0 | b1 | d0 | d1

def isBody : W → Prop
  | .b0 => True
  | .b1 => True
  | .d0 => False
  | .d1 => False

def isDirector : W → Prop
  | .b0 => False
  | .b1 => False
  | .d0 => True
  | .d1 => True

def isB0 : W → Prop
  | .b0 => True
  | .b1 => False
  | .d0 => False
  | .d1 => False

def isB1 : W → Prop
  | .b0 => False
  | .b1 => True
  | .d0 => False
  | .d1 => False

/-- Nothing has the property. -/
def noneP : W → Prop := fun _ => False

/-- Bodies regularly attain (or tend to) the one end. -/
def bodyEnd : W → Unit → Prop := fun x _ => isBody x

def allEnd : W → Unit → Prop := fun _ _ => True

def noEnd : W → Unit → Prop := fun _ _ => False

/-- Two archers: `d0` directs `b0`, `d1` directs `b1`. -/
def twoDirects : W → W → Unit → Prop
  | .d0, x, _ => isB0 x
  | .d1, x, _ => isB1 x
  | .b0, _, _ => False
  | .b1, _, _ => False

/-- One governor: `d0` directs both bodies. -/
def oneDirects : W → W → Unit → Prop
  | .d0, x, _ => isBody x
  | .d1, _, _ => False
  | .b0, _, _ => False
  | .b1, _, _ => False

def noDirects : W → W → Unit → Prop := fun _ _ _ => False

/-- Directors are moved (their reason and will are mutable). -/
def directorsMoved : W → Unit → Prop := fun x _ => isDirector x

def nothingMoved : W → Unit → Prop := fun _ _ => False

def noMoves : W → W → Unit → Prop := fun _ _ _ => False

end TruthCore.Results.Aquinas.SummaTheologiae.QuintaViaModels
