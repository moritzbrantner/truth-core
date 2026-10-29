import TruthCore.Results.Alternatives.RespectSwitch.Solution
import TruthCore.Results.Causality.TemporalEventControls.Solution
import TruthCore.Causality.LocalTransmission
import Mathlib.Logic.Relation

/-! Analyst-defined event profiles, not attributed source readings. The fixed
world/profile is implicit; event tokens, beings, respects and clock times are
separate types. No presentism, passage theory, event population, causal direction
or well-foundedness is built into these definitions. Named theories of time are
not asserted to exhaust this model class. -/
namespace TruthCore.Causality.TemporalActualization
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Greek.Aristotle.Physics.Typed

/-- Each causal edge has strictly increasing selected event clock values.
This is an open profile, not a definition of genuine causation. -/
def StrictForward {E T : Type} [LT T] (clock : E → T) (C : E → E → Prop) : Prop :=
  ∀ e f, C e f → clock e < clock f

/-- Backward edges are forbidden, simultaneous ones permitted. -/
def NoBackward {E T : Type} [LT T] (clock : E → T) (C : E → E → Prop) : Prop :=
  ∀ e f, C e f → ¬ clock f < clock e

def HasSimultaneous {E T : Type} (clock : E → T) (C : E → E → Prop) : Prop :=
  ∃ e f, C e f ∧ clock e = clock f

def HasBackward {E T : Type} [LT T] (clock : E → T) (C : E → E → Prop) : Prop :=
  ∃ e f, C e f ∧ clock f < clock e

/-- Coverage of three semantic predicates under a linear clock order, not of a
list of historical metaphysical theories. The middle horn explicitly retains
NoBackward; having a simultaneous edge alone need not exclude backward edges. -/
def DirectionFork {E T : Type} [LT T] (clock : E → T) (C : E → E → Prop) : Prop :=
  StrictForward clock C ∨ (NoBackward clock C ∧ HasSimultaneous clock C) ∨ HasBackward clock C

/-- No nonempty finite directed closed walk, using Mathlib's transitive closure.
This does not exclude an infinite descending causal chain. -/
def EventAcyclic {E : Type} (C : E → E → Prop) : Prop :=
  ∀ e, ¬ Relation.TransGen C e e

/-- Pairwise incompatibility is separate from coverage. -/
def DirectionExclusive {E T : Type} [LT T] (clock : E → T) (C : E → E → Prop) : Prop :=
  (¬ (StrictForward clock C ∧ (NoBackward clock C ∧ HasSimultaneous clock C))) ∧
  (¬ (StrictForward clock C ∧ HasBackward clock C)) ∧
  (¬ ((NoBackward clock C ∧ HasSimultaneous clock C) ∧ HasBackward clock C))

/-- Universal mathematical certificate; linearity is explicit, not claimed of
actual time. It separates coverage, exclusivity and the strict branch consequence. -/
def Framework : Prop :=
  ∀ (E T : Type) [LinearOrder T] (clock : E → T) (C : E → E → Prop),
    DirectionFork clock C ∧ DirectionExclusive clock C ∧
      (StrictForward clock C → EventAcyclic C)

/-- An explicit open event-to-motion bridge. An edge's target event supplies its
respect and exercise time; the mover may exercise while that target is occurring.
No assertion that its own process has already finished is made. -/
def MotionProjection {E B R T : Type} (clock : E → T) (bearer : E → B)
    (respect : E → R) (C : E → E → Prop) (Moves : T → B → B → R → Prop) : Prop :=
  ∀ e f, C e f → Moves (clock f) (bearer e) (bearer f) (respect f)

/-- Time-sliced lifts of the SAME existing canonical act/potency predicates.
Their philosophical warrant and the event projection remain open. -/
def LocatedMotion {B R T : Type} (Moves : T → B → B → R → Prop)
    (Moved : T → B → R → Prop) : Prop :=
  ∀ t, MovingIsInTheMovedReading (Moves t) (Moved t)
def PotentialMotion {B R T : Type} (Moved Potency : T → B → R → Prop) : Prop :=
  ∀ t, MovedOnlyAsInPotencyReading (Moved t) (Potency t)
def ActualMover {B R T : Type} (Moves : T → B → B → R → Prop)
    (Actual : T → B → R → Prop) : Prop :=
  ∀ t, MovesOnlyAsInActReading (Moves t) (Actual t)
def NotBoth {B R T : Type} (Actual Potency : T → B → R → Prop) : Prop :=
  ∀ t, NotActAndPotencyInSameRespectReading (Actual t) (Potency t)

/-- Reciprocal EVENT edges must be simultaneous and have different target
respects under the stated temporal and canonical local premises. This says
nothing about reciprocal BEING edges produced by distinct tokens over time. -/
def ReciprocalConstraint {E R T : Type} (clock : E → T) (respect : E → R)
    (C : E → E → Prop) : Prop :=
  ∀ e f, C e f → C f e → clock e = clock f ∧ respect e ≠ respect f

/-- Optional staging data: potency before exercise, attainment no earlier than
exercise. It is an open local interpretation. Staging does not say a cause's
attainment must precede its effect's exercise; overlapping exercise is allowed. -/
def Staged {E B R T : Type} [LT T] [LE T] (onset exercise attained : E → T)
    (bearer : E → B) (respect : E → R) (Potency Actual : T → B → R → Prop) : Prop :=
  ∀ e, onset e < exercise e ∧ exercise e ≤ attained e ∧
    Potency (onset e) (bearer e) (respect e) ∧ Actual (attained e) (bearer e) (respect e)

/-- Forget event identity/time while preserving only participating bearers.
A cycle after this projection is not necessarily an event cycle. -/
def BeingEdge {E B : Type} (bearer : E → B) (C : E → E → Prop) (x y : B) : Prop :=
  ∃ e f, bearer e = x ∧ bearer f = y ∧ C e f

/-- Three event tokens A₀→B₁→A₂: entity feedback, no event cycle. -/
def feedbackC (e f : Fin 3) : Prop := e.val + 1 = f.val
def feedbackBearer (e : Fin 3) : Bool := decide (e.val = 1)

/-- A source-free reciprocal simultaneous control with alternating respects.
Sustaining is a separate stipulated relation (same extension here), not identified
with all temporal causation. Its local activity equations admit all-on/all-off. -/
def circleC (e f : Bool) : Prop := e ≠ f
def circleClock (_ : Bool) : ℤ := 0
def circleMoves (t : ℤ) (y x r : Bool) : Prop := t = 0 ∧ y ≠ x ∧ r = x
def circleMoved (t : ℤ) (x r : Bool) : Prop := t = 0 ∧ r = x
def circleActual (t : ℤ) (x r : Bool) : Prop := (t = 0 ∧ r ≠ x) ∨ 3 ≤ t
def circlePotency (t : ℤ) (x r : Bool) : Prop := (t = 0 ∧ r = x) ∨ t < 0

def Controls : Prop :=
  (StrictForward (fun e : Fin 3 => (e.val : ℤ)) feedbackC ∧ EventAcyclic feedbackC ∧
    BeingEdge feedbackBearer feedbackC false true ∧ BeingEdge feedbackBearer feedbackC true false) ∧
  (NoBackward circleClock circleC ∧ HasSimultaneous circleClock circleC ∧
    ¬ StrictForward circleClock circleC ∧ ¬ EventAcyclic circleC ∧
    MotionProjection circleClock id id circleC circleMoves ∧
    LocatedMotion circleMoves circleMoved ∧ PotentialMotion circleMoved circlePotency ∧
    ActualMover circleMoves circleActual ∧ NotBoth circleActual circlePotency ∧
    ReciprocalConstraint circleClock id circleC ∧
    (∀ e, ∃ f, circleC f e) ∧
    (∃ sustains : Bool → Bool → Prop, sustains = circleC ∧
      (∀ e, (True ↔ ∃ f, sustains f e ∧ True)) ∧
      (∀ e, (False ↔ ∃ f, sustains f e ∧ False)))) ∧
  (HasBackward (fun e : Bool => if e then (1 : ℤ) else 0) circleC) ∧
  (StrictForward (fun n : ℕ => -(n : ℤ)) (fun y x => y = x + 1) ∧
    EventAcyclic (fun y x : ℕ => y = x + 1) ∧
    ¬ WellFounded (fun y x : ℕ => y = x + 1)) ∧
  (Staged (fun _ : Bool => (-1 : ℤ)) circleClock (fun _ => (3 : ℤ)) id id
      circlePotency circleActual ∧
    circleC false true ∧ ¬ ((3 : ℤ) < circleClock true)) ∧
  TruthCore.Causality.TemporalEventControls.Controls

end TruthCore.Causality.TemporalActualization
