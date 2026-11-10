module

public import TruthCore.Causality.ActualEuclidean

/-!
# Tolerance-based origin essentialism as a rival of Euclidean access at the actual world

Analyst formulation for the modal spine to "God exists" (stage one); attribution
deferred. The rival is modelled on tolerance-based origin essentialism (the
"possibly possible but not possible" argument from small variations in a
thing's origin); no source claim is made here.

Ordinary meaning. Read worlds as complete histories and access as metaphysical
possibility. A thing could have originated from slightly different material,
but not from wholly different material. So a history in which its origin
differs a little from the actual one is possible relative to the actual
history, and conversely (the difference is the same seen from either side).
Two histories that differ from the actual one in opposite directions may differ
from each other by more than the tolerance; then neither is possible relative
to the other. `ToleranceNonEuclideanAt frame w` says exactly that: access is
reflexive and symmetric, and two successors of `w` fail to access each other.

Example. `Control.tolerance` below: worlds are origin offsets −1, 0, +1, the
actual world is 0, and access holds when the offsets differ by at most 1.
Counterexample. Every Euclidean frame, and `ActualEuclidean.Control.clustered`
(which is not symmetric and satisfies `EuclideanAt` at `actual`).

Distinction from the stepwise rival `SpineRivalsStageOne.ReflexiveNonEuclidean`.
That rival is global and its witness `stepwise` fails `EuclideanAt` at `actual`
only because a successor does not see `actual` back, i.e. by a failure of
symmetry. The tolerance rival keeps symmetry (the B axiom) and fails `EuclideanAt`
at the actual world itself, between two successors. It implies the stepwise
rival's statement (`toleranceReflexiveNonEuclidean` in the results module).

Structural properties: reflexive and symmetric by definition; not transitive
and not Euclidean at `w`. Applicability to reality remains OPEN; the rival is
neither asserted nor refuted here.
-/

@[expose] public section

namespace TruthCore.Causality.ToleranceOriginRival

open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Modal.TemporalHistory
open TruthCore.Causality.ActualEuclidean (EuclideanAt)

/-- Reflexive and symmetric access, with two successors of `w` that do not
access each other. Incompatible with `EuclideanAt frame w` by its third
conjunct. -/
def ToleranceNonEuclideanAt {W : Type} (frame : TruthCore.Modal.Frame W) (w : W) : Prop :=
  (∀ a, frame.access a a) ∧ (∀ a b, frame.access a b → frame.access b a) ∧
    ∃ a b, frame.access w a ∧ frame.access w b ∧ ¬ frame.access a b

namespace Control

/-- Origin offsets of one individual's origin: one step below, the actual
origin, one step above. -/
inductive Origin where
  | minus | actual | plus
  deriving DecidableEq

/-- Access iff the offsets differ by at most one step: only `minus` and `plus`
fail to access each other. -/
def tolerance : TruthCore.Modal.Frame Origin :=
  ⟨fun a b => ¬ ((a = Origin.minus ∧ b = Origin.plus) ∨ (a = Origin.plus ∧ b = Origin.minus))⟩

/-- The closure reading: possible according to some chain of tolerable steps.
On three offsets every world reaches every world. -/
def chained : TruthCore.Modal.Frame Origin := ⟨fun _ _ => True⟩

/-- Individual `false` exists at `actual` and `plus` and is present there at
every time; individual `true` exists at `plus` only and is present there at
time 1 only. Nothing exists at `minus`. -/
def toleranceHistory : History Origin Bool Nat where
  ontic := { frame := tolerance,
             ExistsAt := fun w x => (x = false ∧ w ≠ Origin.minus) ∨ (x = true ∧ w = Origin.plus),
             Causes := fun _ _ _ => False }
  IsAt := fun w x t => (x = false ∧ w ≠ Origin.minus) ∨ (x = true ∧ w = Origin.plus ∧ t = 1)
  now := 1

/-- The same assignment under the chained (closure) frame. -/
def chainedHistory : History Origin Bool Nat :=
  { toleranceHistory with ontic := { toleranceHistory.ontic with frame := chained } }

/-- (1) The tolerance frame satisfies the rival at `actual`, is reflexive there,
and is not Euclidean at `actual`. (2) On `toleranceHistory`, presence-to-existence,
inert emptiness and the possible contingent-free past at `actual` hold, and no
concrete individual is necessary at `actual`. (3) Under the chained reading
of the same assignment, Euclidean access at `actual` holds, the possible
contingent-free past at `actual` fails, and the conclusion still fails. -/
def Certificate : Prop :=
  (ToleranceNonEuclideanAt tolerance Origin.actual ∧
    NecessarilyUnderived.ActualReflexive toleranceHistory.ontic Origin.actual ∧
    ¬ EuclideanAt tolerance Origin.actual) ∧
  (CountTemporalNecessity.HistoryPresenceActual toleranceHistory ∧
    InertEmptiness.EmptinessStaysEmpty toleranceHistory InertEmptiness.Control.all ∧
    InertEmptiness.PossiblyContingentsAbsentThenPresent toleranceHistory
      InertEmptiness.Control.all Origin.actual ∧
    ¬ BruteFoundationBoundary.NecessaryConcreteAt
        ⟨toleranceHistory.ontic, InertEmptiness.Control.all, fun _ _ _ => False⟩
        Origin.actual) ∧
  (EuclideanAt chained Origin.actual ∧
    ¬ InertEmptiness.PossiblyContingentsAbsentThenPresent chainedHistory
      InertEmptiness.Control.all Origin.actual ∧
    ¬ BruteFoundationBoundary.NecessaryConcreteAt
        ⟨chainedHistory.ontic, InertEmptiness.Control.all, fun _ _ _ => False⟩
        Origin.actual)

end Control

end TruthCore.Causality.ToleranceOriginRival
