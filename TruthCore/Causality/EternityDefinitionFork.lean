module

public import TruthCore.Results.Aquinas.SummaTheologiae.ImmutableIsBoethianEternal.Solution
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.InfinityEternity
public import TruthCore.Logic.ExcludedMiddle

/-! Analyst calibrations of the root's independent primitive Eternal predicate.
Reuse the existing partial Boethian operational account without claiming it
captures perfecta possessio or establishes source identity. Existential life
plus Interminable permits succession; on arbitrary admitted LT comparisons it
means absence of the existing LifeBeginsOrEnds witness, not an independently
proved complete temporal continuum or atemporal ontology. -/

@[expose] public section
namespace TruthCore.Causality.EternityDefinitionFork
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- The existing core Bool order, fixed before the frame-indexed instance. -/
def boolEarlier : Bool → Bool → Prop := (· < ·)

structure Frame where
  Being : Type
  Respect : Type
  Time : Type
  State : Type
  earlier : Time → Time → Prop
  InPotency : Being → Respect → Prop
  LivesAt : Being → Time → Prop
  lifeStateAt : Being → Time → State
  Eternal : Being → Prop

instance (f : Frame) : LT f.Time := ⟨f.earlier⟩

def EndlessLife (f : Frame) (x : f.Being) : Prop :=
  (∃ t, f.LivesAt x t) ∧ Interminable f.LivesAt x

def BoethianDefinition (f : Frame) : Prop :=
  ∀ x, f.Eternal x ↔ BoethianEternal f.LivesAt f.lifeStateAt x

def EndlessDefinition (f : Frame) : Prop :=
  ∀ x, f.Eternal x ↔ EndlessLife f x

/-- Weak transfer sufficient for the existing primitive eternity route. It need
not forbid Eternal attribution outside the supplied operational Boethian class. -/
def BoethianRecognition (f : Frame) : Prop :=
  ∀ x, BoethianEternal f.LivesAt f.lifeStateAt x → f.Eternal x

def NamedCoverage (f : Frame) : Prop := BoethianDefinition f ∨ EndlessDefinition f
def Other (f : Frame) : Prop := ¬ BoethianDefinition f ∧ ¬ EndlessDefinition f
def EndlessDefinitionFails (f : Frame) : Prop := ¬ EndlessDefinition f

def DefinitionFork : Prop := ∀ f, NamedCoverage f ∨ Other f

/-- Supplied two-time order reuses core Bool's LT; no causal or philosophical
order is inferred from it. -/
def successive : Frame where
  Being := Unit
  Respect := Unit
  Time := Bool
  State := Bool
  earlier := boolEarlier
  InPotency := fun _ _ => False
  LivesAt := fun _ _ => True
  lifeStateAt := fun _ t => t
  Eternal := fun _ => True

/-- Same nonvacuous typed eternity profile as the previous joint control, with
primitive Eternal interpreted independently as false. -/
def unrecognized : Frame where
  Being := Unit
  Respect := Unit
  Time := Bool
  State := Bool
  earlier := boolEarlier
  InPotency := fun _ _ => False
  LivesAt := fun _ _ => True
  lifeStateAt := fun _ _ => false
  Eternal := fun _ => False

def overlap : Frame := { unrecognized with Eternal := fun _ => True }

/-- No life in the admitted frame, but positive primitive attribution: neither
named operational calibration holds. This is not a claimed adequate ontology. -/
def remainder : Frame :=
  { unrecognized with
    LivesAt := fun _ _ => False
    Eternal := fun _ => True }

def Controls : Prop :=
  (EndlessDefinition successive ∧ ¬ BoethianDefinition successive ∧
    EndlessLife successive () ∧ ¬ BoethianEternal successive.LivesAt successive.lifeStateAt ()) ∧
  (BoethianRecognition successive ∧ ¬ BoethianDefinition successive) ∧
  (SuccessionRequiresPotencyReading unrecognized.InPotency unrecognized.LivesAt unrecognized.lifeStateAt ∧
    LifeBoundaryRequiresPotencyReading unrecognized.InPotency unrecognized.LivesAt ∧
    PureActLivesReading unrecognized.InPotency unrecognized.LivesAt ∧
    PureAct unrecognized.InPotency () ∧
    ¬ ImmutableIsEternalReading unrecognized.InPotency unrecognized.Eternal) ∧
  (BoethianDefinition overlap ∧ EndlessDefinition overlap) ∧ Other remainder

end TruthCore.Causality.EternityDefinitionFork
