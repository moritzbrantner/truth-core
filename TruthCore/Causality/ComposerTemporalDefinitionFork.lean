module

public import TruthCore.Results.Aquinas.SummaTheologiae.CompositeUnitingCauseFromUnion.Solution
public import TruthCore.Logic.ExcludedMiddle

/-! Analyst formulations of the temporal scope of efficient causing, attribution
 deferred. The existing uniting and causal-responsibility predicates are reused.
 A new time index is needed because the canonical efficient relation is read at
 one selected time. An existential temporal reading is one interpretation of
 time-neutral production; it does not cover atemporal causation.

 A builder's past construction is a motivating example of production without
 present activity; a currently operating support is an example of activity at
 the selected time. These are illustrations, not premises establishing that
 any actual construction/support satisfies the predicates. Efficient causation
 remains independent of mere chronological succession, uniting, and causing
 esse. No persistence, priority, asymmetry, or well-foundedness is built in.
-/

@[expose] public section
namespace TruthCore.Causality.ComposerTemporalDefinitionFork

open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article7Uniting

universe u v w

/-- A fixed admitted time domain and selected evaluation time. `EfficientAt`
means efficient causal activity at that time, in the canonical efficient sense;
its applicability to actual cases remains an open framework commitment.
`Attributed` is the independently supplied, temporally unspecified attribution
whose competing calibrations are investigated. -/
structure Frame where
  Being : Type u
  Respect : Type v
  Time : Type w
  now : Time
  EfficientAt : Time → Being → Being → Respect → Prop
  Attributed : Being → Being → Respect → Prop
  Unites : Being → Being → Being → Being → Prop

def Current (f : Frame) := f.EfficientAt f.now
def Temporal (f : Frame) (c x : f.Being) (r : f.Respect) : Prop :=
  ∃ t, f.EfficientAt t c x r

def CurrentDefinition (f : Frame) : Prop :=
  ∀ c x r, f.Attributed c x r ↔ Current f c x r

def TemporalDefinition (f : Frame) : Prop :=
  ∀ c x r, f.Attributed c x r ↔ Temporal f c x r

def CurrentDefinitionFails (f : Frame) : Prop := ¬ CurrentDefinition f

def NamedCoverage (f : Frame) : Prop := CurrentDefinition f ∨ TemporalDefinition f

def Other (f : Frame) : Prop := ¬ CurrentDefinition f ∧ ¬ TemporalDefinition f

def DefinitionFork : Prop := ∀ f : Frame.{u,v,w}, NamedCoverage f ∨ Other f

/-- A transfer only on actual uniting tuples, weaker than persistence of every
 efficient activity. Not a definition of efficient causation. -/
def UniterPersistence (f : Frame) : Prop :=
  ∀ c a b x, f.Unites c a b x →
    (∃ r, Temporal f c x r) → ∃ r, Current f c x r

def GlobalPersistence (f : Frame) : Prop :=
  ∀ c x r, Temporal f c x r → Current f c x r

def AttributedComposer (f : Frame) : Prop :=
  UnitingCauseIsEfficientCauseReading f.Unites f.Attributed

def TemporalComposer (f : Frame) : Prop :=
  UnitingCauseIsEfficientCauseReading f.Unites (Temporal f)

def CurrentComposer (f : Frame) : Prop :=
  UnitingCauseIsEfficientCauseReading f.Unites (Current f)

def AllTimeNoSelf (f : Frame) : Prop :=
  ∀ t, NothingIsEfficientCauseOfItselfReading (f.EfficientAt t)

def CurrentNoSelf (f : Frame) : Prop :=
  NothingIsEfficientCauseOfItselfReading (Current f)

/-- The exact existing composite conclusion, using the existing being-cause
 relation independently of the temporal efficient-cause index. -/
def CompositeConclusion (f : Frame) (Composite : f.Being → Prop)
    (CausesIn : f.Being → f.Being → f.Respect → Prop) (esse : f.Respect) : Prop :=
  CompositeHasAUnitingCauseReading Composite CausesIn esse

/-- Finite controls below are interpretations, not metaphysical possibilities. -/
def pastBuilder : Frame where
  Being := Bool
  Respect := Unit
  Time := Bool
  now := true
  EfficientAt := fun t c x _ => t = false ∧ c = false ∧ x = true
  Attributed := fun c x _ => c = false ∧ x = true
  Unites := fun c _ _ x => c = false ∧ x = true

/-- Past self-production is allowed by this interpretation's current-time ban;
 it violates the separately stated all-time ban. -/
def pastSelf : Frame where
  Being := Bool
  Respect := Unit
  Time := Bool
  now := true
  EfficientAt := fun t c x _ => t = false ∧ c = x
  Attributed := fun c x _ => c = x
  Unites := fun c _ _ x => c = x

def selfComposite (_ : Bool) : Prop := True
def selfComponent (_ _ : Bool) : Prop := True
def selfCauses (c x : Bool) (_ : Unit) : Prop := c = x

/-- Both calibrations can hold when the admitted causal activity persists. -/
def overlap : Frame where
  Being := Bool
  Respect := Unit
  Time := Bool
  now := true
  EfficientAt := fun _ c x _ => c = false ∧ x = true
  Attributed := fun c x _ => c = false ∧ x = true
  Unites := fun c _ _ x => c = false ∧ x = true

/-- A richer unspecified attribution can fall outside both temporal calibrations;
 this does not identify it with atemporal causation. -/
def remainder : Frame where
  Being := Unit
  Respect := Unit
  Time := Unit
  now := ()
  EfficientAt := fun _ _ _ _ => False
  Attributed := fun _ _ _ => True
  Unites := fun _ _ _ _ => True

/-- Persistence restricted to actual uniters need not persist unrelated activity. -/
def localOnly : Frame where
  Being := Bool
  Respect := Unit
  Time := Bool
  now := true
  EfficientAt := fun t c x _ => (c = false ∧ x = true) ∨ (t = false ∧ c = true ∧ x = false)
  Attributed := fun c x _ => c ≠ x
  Unites := fun c _ _ x => c = false ∧ x = true

/-- Exact finite controls registered separately from philosophical premises. -/
def BoundaryControls : Prop :=
    (TemporalDefinition pastBuilder ∧ TemporalComposer pastBuilder ∧
      AllTimeNoSelf pastBuilder ∧ ¬ CurrentComposer pastBuilder ∧ ¬ CurrentDefinition pastBuilder) ∧
    (TemporalComposer pastSelf ∧ CurrentNoSelf pastSelf ∧ ¬ AllTimeNoSelf pastSelf) ∧
    (CurrentDefinition overlap ∧ TemporalDefinition overlap ∧ CurrentComposer overlap) ∧
    Other remainder ∧
    (UniterPersistence localOnly ∧ ¬ GlobalPersistence localOnly)


/-- Exact finite controls registered separately from philosophical premises. -/
def PastSelfControl : Prop :=
    TemporalComposer pastSelf ∧ CurrentNoSelf pastSelf ∧
    CompositeHasTwoDistinctComponentsReading selfComposite selfComponent ∧
    DiverseUnitedOnlyThroughUnitingCauseReading selfComponent pastSelf.Unites ∧
    UnitingCauseCausesBeingReading pastSelf.Unites selfCauses () ∧
    selfComposite false ∧
    ¬ CompositeConclusion pastSelf selfComposite selfCauses ()

end TruthCore.Causality.ComposerTemporalDefinitionFork
