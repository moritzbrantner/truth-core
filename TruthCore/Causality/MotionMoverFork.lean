module
public import TruthCore.Greek.Aristotle.Physics.Typed.Motion
@[expose] public section
namespace TruthCore.Causality.MotionMoverFork
open TruthCore.Greek.Aristotle.Physics.Typed
open TruthCore.Latin.Aquinas.SummaTheologiae
/-- MOTION_1: a witness of the existing primitive broad reduction predicate.
The wrapper does not assert independent applicability of that primitive. -/
inductive BroadMotion {B R : Type} (moved : B → R → Prop) (x : B) (r : R) : Prop
  | intro : moved x r → BroadMotion moved x r
/-- MOTION_2: broad reduction restricted to an explicitly physical respect.
Which respects are physical remains a supplied semantic classification. -/
inductive PhysicalMotion {B R : Type} (physical : R → Prop)
    (moved : B → R → Prop) (x : B) (r : R) : Prop
  | intro : physical r → moved x r → PhysicalMotion physical moved x r
/-- Same-respect per-se mover, with no distinctness requirement. -/
inductive SomeMover {B R : Type} (moves : B → B → R → Prop) (x : B) (r : R) : Prop
  | intro (y : B) : moves y x r → SomeMover moves x r
/-- Same-respect mover that is distinct from the moved subject.
This is narrower than Physics VIII.5's some-respect MovedByAnother. -/
inductive AnotherMover {B R : Type} (moves : B → B → R → Prop) (x : B) (r : R) : Prop
  | intro (y : B) : y ≠ x → moves y x r → AnotherMover moves x r
/-- Per-accidens link only: no per-se consequence is built into this type. -/
inductive AccidentalMover {B R : Type} (accidental : B → B → R → Prop)
    (x : B) (r : R) : Prop
  | intro (y : B) : accidental y x r → AccidentalMover accidental x r
/-- Respect-free distinct-mover reading used by Physics VIII.5. -/
inductive AnotherMoverAnyRespect {B R : Type} (moves : B → B → R → Prop) (x : B) : Prop
  | intro : MovedByAnother moves x → AnotherMoverAnyRespect moves x
inductive MotionSense | broad | physical
inductive MoverSense | something | another | accidental
/-- Meaning-bearing interpretation of the finite motion fork. -/
def MotionMeaning {B R : Type} (physical : R → Prop) (moved : B → R → Prop)
    (s : MotionSense) (x : B) (r : R) : Prop :=
  match s with
  | .broad => BroadMotion moved x r
  | .physical => PhysicalMotion physical moved x r
/-- Meaning-bearing interpretation of the finite mover fork. -/
def MoverMeaning {B R : Type} (moves accidental : B → B → R → Prop)
    (s : MoverSense) (x : B) (r : R) : Prop :=
  match s with
  | .something => SomeMover moves x r
  | .another => AnotherMoverAnyRespect moves x
  | .accidental => AccidentalMover accidental x r
/-- Coverage for the route's broad reductions; residual is an explicit class,
not an identification of nonphysical motion with physical change. -/
def MotionCoverage {B R : Type} (physical residual : R → Prop)
    (moved : B → R → Prop) : Prop :=
  ∀ x r, moved x r → physical r ∨ residual r
/-- Optional partition constraint; the weakest root derivation needs only coverage. -/
def MotionExclusive {R : Type} (physical residual : R → Prop) : Prop :=
  ∀ r, ¬ (physical r ∧ residual r)
def ResidualHasMover {B R : Type} (residual : R → Prop)
    (moved : B → R → Prop) (moves : B → B → R → Prop) : Prop :=
  ∀ x r, residual r → moved x r → ∃ y, moves y x r
/-- Open conversion obligation, restricted to subjects with accidental links.
No universal identification of the two mover relations is asserted. -/
def AccidentalHasPerSeMover {B R : Type} (moves accidental : B → B → R → Prop) : Prop :=
  ∀ x r, AccidentalMover accidental x r → SomeMover moves x r
def AnotherGivesSomething {B R : Type} (moves : B → B → R → Prop) : Prop :=
  ∀ x r, AnotherMover moves x r → SomeMover moves x r
def MoverForkSound {B R : Type} (moves accidental : B → B → R → Prop) : Prop :=
  ∀ s x r, MoverMeaning moves accidental s x r → ∃ q, SomeMover moves x q
def AnotherAnyGivesSomethingAny {B R : Type} (moves : B → B → R → Prop) : Prop :=
  ∀ x, AnotherMoverAnyRespect moves x → ∃ r, SomeMover moves x r
def PhysicalGivesBroad {B R : Type} (physical : R → Prop) (moved : B → R → Prop) : Prop :=
  ∀ x r, PhysicalMotion physical moved x r → BroadMotion moved x r
/-- Finite selected interpretation: coverage and uniqueness concern a use,
not disjoint extensions of meanings (another already entails something). -/
def MoverCoverage (selected : MoverSense → Prop) : Prop := ∃ s, selected s
def MoverExclusive (selected : MoverSense → Prop) : Prop :=
  ∀ s t, selected s → selected t → s = t
def MotionReadingCoverage (selected : MotionSense → Prop) : Prop := ∃ s, selected s
def MotionReadingExclusive (selected : MotionSense → Prop) : Prop :=
  ∀ s t, selected s → selected t → s = t
/-- Both finite motion readings inherit same-respect mover coverage. -/
def MotionForkSound {B R : Type} (physical : R → Prop) (moved : B → R → Prop)
    (moves : B → B → R → Prop) : Prop :=
  ∀ s x r, MotionMeaning physical moved s x r → ∃ y, moves y x r
def Controls : Prop :=
  (∃ (physical residual : Bool → Prop) (moved : Unit → Bool → Prop)
      (moves : Unit → Unit → Bool → Prop),
    MotionCoverage physical residual moved ∧ MotionExclusive physical residual ∧
    EveryPhysicalMotionHasAPerSeMoverReading physical moved moves ∧
    ResidualHasMover residual moved moves ∧ moved () false ∧ moved () true ∧
    physical false ∧ residual true) ∧
  (∃ (p q : Unit → Prop) (m : Unit → Unit → Prop) (a : Unit → Unit → Unit → Prop),
    MotionCoverage p q m ∧ ResidualHasMover q m a ∧ ¬ ReducedOnlyByAMoverReading m a) ∧
  (∃ (p q : Unit → Prop) (m : Unit → Unit → Prop) (a : Unit → Unit → Unit → Prop),
    EveryPhysicalMotionHasAPerSeMoverReading p m a ∧ ResidualHasMover q m a ∧
    ¬ ReducedOnlyByAMoverReading m a) ∧
  (∃ (p q : Unit → Prop) (m : Unit → Unit → Prop) (a : Unit → Unit → Unit → Prop),
    MotionCoverage p q m ∧ EveryPhysicalMotionHasAPerSeMoverReading p m a ∧
    ¬ ReducedOnlyByAMoverReading m a) ∧
  (SomeMover (fun _ _ _ : Unit => True) () () ∧
    ¬ AnotherMover (fun _ _ _ : Unit => True) () ()) ∧
  (AccidentalMover (fun _ _ _ : Unit => True) () () ∧
    ¬ SomeMover (fun _ _ _ : Unit => False) () ()) ∧
  (MoverCoverage (fun s => s = .another) ∧ MoverExclusive (fun s => s = .another)) ∧
  (MotionReadingCoverage (fun s => s = .broad) ∧
    MotionReadingExclusive (fun s => s = .broad)) ∧
  (BroadMotion (fun _ _ : Unit => True) () () ∧
    ¬ PhysicalMotion (fun _ : Unit => False) (fun _ _ : Unit => True) () ()) ∧
  AccidentalHasPerSeMover (fun _ _ _ : Unit => True) (fun _ _ _ : Unit => True)
end TruthCore.Causality.MotionMoverFork
