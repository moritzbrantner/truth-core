module
public import TruthCore.Causality.MotionMoverFork
@[expose] public section
namespace TruthCore.Causality.PartMediatedSelfMotion
open TruthCore.Causality.MotionMoverFork
open TruthCore.Latin.Aquinas.SummaTheologiae
/-- A bounded organism: two proper parts and their whole. Not an empirical anatomy. -/
inductive Carrier | whole | motor | load deriving DecidableEq
inductive Respect | displacement | temperature deriving DecidableEq
/-- Proper membership is extensional and excludes the whole itself. -/
def Part (p w : Carrier) : Prop :=
  w = .whole ∧ (p = .motor ∨ p = .load)
/-- Two actually distinct component roles in the displacement event. -/
def ComponentMoves (a b : Carrier) (r : Respect) : Prop :=
  a = .motor ∧ b = .load ∧ r = .displacement
/-- Internal coordination requires two proper members, retaining the event's respect.
This is a derived organism predicate, not a primitive self-edge. -/
inductive InternalMotion (w : Carrier) (r : Respect) : Prop
  | intro (a b : Carrier) : Part a w → Part b w →
      ComponentMoves a b r → InternalMotion w r
/-- Lifting only the patient preserves the motor as agent. This is an explicit
relation construction; applicability as whole motion is an OPEN bridge. -/
def PatientLift (a w : Carrier) (r : Respect) : Prop :=
  ∃ b, Part b w ∧ ComponentMoves a b r
/-- Lifting both roles forgets component identity. It cannot be used as if
component-level irreflexivity had survived the quotient. -/
def AggregateLift (v w : Carrier) (r : Respect) : Prop :=
  ∃ a b, Part a v ∧ Part b w ∧ ComponentMoves a b r
/-- No implicit event in another respect: only the load is displaced. -/
def ComponentMoved (b : Carrier) (r : Respect) : Prop :=
  b = .load ∧ r = .displacement
/-- Whole displacement is a separate observation, not deduced from membership. -/
def WholeMoved (w : Carrier) (r : Respect) : Prop :=
  w = .whole ∧ r = .displacement
/-- Local bridge needed for a supplied whole-mover relation. Only the actual
internal event is covered, without requiring all part motion to move its whole. -/
def LocalLift (moves : Carrier → Carrier → Respect → Prop) : Prop :=
  ∀ a b w r, Part a w → Part b w → ComponentMoves a b r → moves a w r
def InternalHasDistinctMover (moves : Carrier → Carrier → Respect → Prop) : Prop :=
  ∀ w r, InternalMotion w r → AnotherMover moves w r
/-- Populated non-entailments, with explicit roles and respect. -/
def Controls : Prop :=
  InternalMotion .whole .displacement ∧
  NothingMovesItselfInSameRespectReading ComponentMoved ComponentMoves ∧
  AnotherMover ComponentMoves .load .displacement ∧
  AnotherMover PatientLift .whole .displacement ∧
  (¬ ∃ a, ¬ Part a .whole ∧ PatientLift a .whole .displacement) ∧
  (¬ SomeMover ComponentMoves .whole .displacement) ∧
  (¬ NothingMovesItselfInSameRespectReading WholeMoved AggregateLift) ∧
  (¬ InternalHasDistinctMover ComponentMoves) ∧
  (¬ InternalHasDistinctMover AggregateLift) ∧
  (¬ InternalMotion .whole .temperature)
end TruthCore.Causality.PartMediatedSelfMotion
