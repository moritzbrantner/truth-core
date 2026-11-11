module

public import TruthCore.Mereology.ProcessTurnover

/-! Analyst operational candidate for #327, not a definition of all biological life.
Roles name locally identified production capacities, never organisms or souls.
The rules are declared intervention mechanisms, not inferred from a trajectory.
All material tokens may change while role occupancy persists. -/
@[expose] public section
namespace TruthCore.Mereology.LifeRestricted327

/-- Two role occupancies: substrate-processing and boundary-production. Their
local physical realization and the boundary of the tested system remain open. -/
structure State where
  processing : Bool
  boundary : Bool
  deriving DecidableEq

def full : State := ⟨true, true⟩
def empty : State := ⟨false, false⟩
def noProcessing : State := ⟨false, true⟩
def noBoundary : State := ⟨true, false⟩

/-- Fresh role realizers are produced only with feed, processing and retained
boundary. Previous realizers are discarded each tick; these are occupancy
outputs, not numerical identities of the incoming/outgoing material tokens. -/
def regenerate (feed : Bool) (s : State) : State :=
  ⟨feed && s.processing && s.boundary, feed && s.processing && s.boundary⟩

/-- An external replacer produces the same actual occupancy sequence without
requiring the local production capacities. No thesis about every pump is made. -/
def replaceExternally (feed : Bool) (_ : State) : State := ⟨feed, feed⟩

/-- A restricted affirmative maintenance criterion: a nonempty productive state
is regenerated, complete removal stays empty, and knocking out either capacity
abolishes the other's next output. This is more than an observed fixed point.
It is not sufficient by definition for life, organismhood or substantial unity. -/
def Reciprocal (rule : State → State) : Prop :=
  rule full = full ∧ rule empty = empty ∧
    (rule noProcessing).boundary = false ∧
    (rule noBoundary).processing = false

/-- A material token is indexed by tick and role. Time is not an organism
identity criterion; this models complete cohort replacement under active feed. -/
structure Token where
  tick : Nat
  role : Bool
  deriving DecidableEq

def present (n : Nat) (c : Token) : Prop := c.tick = n

/-- Every tick freshly realizes both roles under continued feed. -/
def run : Nat → State
  | 0 => full
  | n + 1 => regenerate true (run n)

/-- A one-tick feed interruption kills this fragile mechanism; restoring feed
alone does not resurrect its lost production capacities. This is not a general
claim that starvation or dormancy is death in actual organisms. -/
def stopped : State := regenerate false full

def Certificate : Prop :=
  Reciprocal (regenerate true) ∧
  ¬ Reciprocal (replaceExternally true) ∧
  regenerate true full = replaceExternally true full ∧
  (∀ n, run n = full) ∧
  (∀ n c, present n c → ¬ present (n + 1) c) ∧
  stopped = empty ∧ regenerate true stopped = empty ∧
  (∀ (P : Type) (carrier : TruthCore.Mereology.Vitalism.Phase → P)
    (parts : P → TruthCore.Mereology.Vitalism.Component → Prop),
    TruthCore.Mereology.ProcessTurnover.PreservesContinuity
      (TruthCore.Mereology.Vitalism.scenario False False) carrier →
    ¬ TruthCore.Mereology.ProcessTurnover.FixedExtension
      (TruthCore.Mereology.Vitalism.scenario False False) carrier parts)
end TruthCore.Mereology.LifeRestricted327
