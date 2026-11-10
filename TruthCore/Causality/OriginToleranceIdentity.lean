module

public import TruthCore.Causality.ToleranceOriginRival

/-!
# An origin interface for the tolerance rival of Euclidean access at the actual world

Analyst formulation for the modal spine to "God exists" (stage one); attribution
deferred. It restores the commitment that `ToleranceOriginRival` left out: the
tolerance rival concerns one and the same individual, existing in neighbouring
worlds with a slightly varied material origin.

Ordinary meaning. `OriginInterface` assigns to each world and individual an
origin (read: the portion of matter it came from; the value is idle where the
individual does not exist) and a closeness relation `near` on origins (read:
"differs by no more than the tolerance"). Identity across worlds is the rigid
identity of the carrier `B`, as in `NecessaryConcreteAt`; no counterpart
relation is introduced.

Encoded commitments (analyst reconstruction, each an open framework input):
* `NearIsTolerance`: closeness is reflexive and symmetric; transitivity is not
  required and is not denied by this premise alone.
* `OriginDeterminesAccess`: `v` is possible relative to `w` iff every individual
  existing at both has near origins there. The "only if" direction is the
  essentialist half (no possible world gives a thing a far origin); the "if"
  direction is a plenitude half (origin closeness is the only constraint).
* `OriginPlenitude`: tolerance is realised: for each concrete individual at `w`
  and each origin near its origin at `w`, some world accessible from `w`
  contains it with that origin.
* `VariedOriginAt`: some concrete individual existing at `w` also exists at two
  worlds accessible from `w` with origins that are not near. The separate
  `OriginDeterminesAccess` premise links that non-closeness to access failure.

Left OPEN: whether origins are the only essential constraint (the "if" half),
vagueness of `near`, kind-relative tolerance, counterpart-theoretic readings,
and independent warrant for the permitted absences and temporal assignment.
Individual deletion and joint deletion of the entire actual roster are different
requirements; neither is `OriginPlenitude`, which preserves its selected
individual. The relation between these commitments and reality is not asserted.

Example: `Control.faithful` below. Counterexample: `Control.restored` satisfies
the commitments but its only individual exists at every world, so the rival
gives no countermodel there. Direct evaluation, not a new registered theorem:
every actual individual in `faithful` can be absent at an accessible world
(`a` at `bMinus`, `b` at `aMinus`), yet `b` is necessary relative to `plus`.
Requiring such deletion at every world would conflict with the existing
`InertEmptiness.earlierNecessary` consequence of the arrival's temporal premises.
That stronger bundle's inconsistency does not make this original model vacuous
or establish that worldwise deletion follows from the origin commitments.
-/

@[expose] public section

namespace TruthCore.Causality.OriginToleranceIdentity

open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Modal.TemporalHistory
open TruthCore.Causality.ActualEuclidean (EuclideanAt)
open TruthCore.Causality.ToleranceOriginRival (ToleranceNonEuclideanAt)

/-- Origins of individuals at worlds and a closeness relation on origins. -/
structure OriginInterface (W B O : Type) where
  near : O → O → Prop
  origin : W → B → O

variable {W B O : Type}

/-- Closeness of origins is reflexive and symmetric. -/
def NearIsTolerance (I : OriginInterface W B O) : Prop :=
  (∀ o, I.near o o) ∧ ∀ o o', I.near o o' → I.near o' o

/-- Access holds exactly when every shared individual has near origins. -/
def OriginDeterminesAccess (m : Ontic W B) (I : OriginInterface W B O) : Prop :=
  ∀ w v, m.frame.access w v ↔
    ∀ x, m.ExistsAt w x → m.ExistsAt v x → I.near (I.origin w x) (I.origin v x)

/-- Every near variation of a concrete individual's origin is realised in an
accessible world containing that individual. -/
def OriginPlenitude (m : Ontic W B) (Concrete : B → Prop) (I : OriginInterface W B O) :
    Prop :=
  ∀ w x, Concrete x → m.ExistsAt w x → ∀ o, I.near (I.origin w x) o →
    ∃ v, m.frame.access w v ∧ m.ExistsAt v x ∧ I.origin v x = o

/-- Some concrete individual existing at `w` exists at two worlds accessible
from `w` with origins that are not near. -/
def VariedOriginAt (m : Ontic W B) (Concrete : B → Prop) (I : OriginInterface W B O)
    (w : W) : Prop :=
  ∃ x, Concrete x ∧ m.ExistsAt w x ∧ ∃ a b, m.frame.access w a ∧ m.frame.access w b ∧
    m.ExistsAt a x ∧ m.ExistsAt b x ∧ ¬ I.near (I.origin a x) (I.origin b x)

namespace Control

/-- Five worlds. Individual `a` (`false`) has origin offsets −1, 0, +1 at
`aMinus`, `actual`, `plus`; individual `b` (`true`) has offsets 0, 0, −1, +1 at
`actual`, `plus`, `bMinus`, `bPlus`. `a` is absent from `bMinus`, `bPlus`;
`b` is absent from `aMinus`. -/
inductive World where
  | aMinus | actual | plus | bMinus | bPlus
  deriving DecidableEq

open TruthCore.Causality.ToleranceOriginRival.Control (Origin tolerance)

def exists' : World → Bool → Prop
  | World.aMinus, x => x = false
  | World.actual, _ => True
  | World.plus, _ => True
  | World.bMinus, x => x = true
  | World.bPlus, x => x = true

def originOf : World → Bool → Origin
  | World.aMinus, _ => Origin.minus
  | World.actual, _ => Origin.actual
  | World.plus, false => Origin.plus
  | World.plus, true => Origin.actual
  | World.bMinus, _ => Origin.minus
  | World.bPlus, _ => Origin.plus

/-- Offsets are near iff they differ by at most one step. -/
def interface : OriginInterface World Bool Origin := ⟨tolerance.access, originOf⟩

/-- Access fails exactly between `aMinus` and `plus` (individual `a` at −1 and
+1) and between `bMinus` and `bPlus` (individual `b` at −1 and +1). -/
def far : World → World → Prop
  | World.aMinus, World.plus => True
  | World.plus, World.aMinus => True
  | World.bMinus, World.bPlus => True
  | World.bPlus, World.bMinus => True
  | _, _ => False

/-- `b` is present everywhere it exists at every time; `a` is present at
`aMinus` and `actual` at every time and at `plus` only at time 1. -/
def isAt : World → Bool → Nat → Prop
  | World.plus, false, t => t = 1
  | w, x, _ => exists' w x

def faithful : History World Bool Nat where
  ontic := { frame := ⟨fun u v => ¬ far u v⟩, ExistsAt := exists', Causes := fun _ _ _ => False }
  IsAt := isAt
  now := 1

/-- The surrogate's three offsets with the varied individual restored: one
individual existing at every offset with that offset as its origin. -/
def restored : Ontic Origin Unit :=
  { frame := tolerance, ExistsAt := fun _ _ => True, Causes := fun _ _ _ => False }

def restoredInterface : OriginInterface Origin Unit Origin := ⟨tolerance.access, fun w _ => w⟩

/-- (1) `faithful` satisfies the four origin commitments; reflexivity at
`actual`, presence-to-existence, inert emptiness and the possible
contingent-free past at `actual` hold; Euclidean access at `actual` and
`NecessaryConcreteAt` at `actual` fail. (2) `restored` satisfies the four
origin commitments and `NecessaryConcreteAt` at the actual offset holds. -/
def Certificate : Prop :=
  (NearIsTolerance interface ∧ OriginDeterminesAccess faithful.ontic interface ∧
    OriginPlenitude faithful.ontic (fun _ => True) interface ∧
    VariedOriginAt faithful.ontic (fun _ => True) interface World.actual) ∧
  (NecessarilyUnderived.ActualReflexive faithful.ontic World.actual ∧
    CountTemporalNecessity.HistoryPresenceActual faithful ∧
    InertEmptiness.EmptinessStaysEmpty faithful (fun _ => True) ∧
    InertEmptiness.PossiblyContingentsAbsentThenPresent faithful (fun _ => True) World.actual ∧
    ¬ EuclideanAt faithful.ontic.frame World.actual ∧
    ¬ BruteFoundationBoundary.NecessaryConcreteAt
        ⟨faithful.ontic, fun _ => True, fun _ _ _ => False⟩ World.actual) ∧
  (NearIsTolerance restoredInterface ∧ OriginDeterminesAccess restored restoredInterface ∧
    OriginPlenitude restored (fun _ => True) restoredInterface ∧
    VariedOriginAt restored (fun _ => True) restoredInterface Origin.actual ∧
    BruteFoundationBoundary.NecessaryConcreteAt
        ⟨restored, fun _ => True, fun _ _ _ => False⟩ Origin.actual)

end Control

end TruthCore.Causality.OriginToleranceIdentity
