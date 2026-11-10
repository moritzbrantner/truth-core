module

public import TruthCore.Causality.OriginToleranceIdentity
public import TruthCore.Causality.InertEmptiness

/-!
# Individual deletion and the origin-tolerance account

Analyst formulation for stage one of the modal spine to "God exists";
attribution deferred.

Ordinary meaning. *Deletion at `w`*: every concrete individual existing at `w`
is absent from some world possible relative to `w`. Equivalently, no concrete
individual existing at `w` is necessary relative to `w` (world-relative
necessity, `NecessaryAt`). It is a local, individual-by-individual claim: it
does not say that one world lacks all of them (joint deletion), and at one world
it says nothing about necessity relative to other worlds.

Three scopes are kept apart: `DeletionAt m Concrete w` (one world),
`AccessibleDeletion m Concrete w` (every world accessible from `w`) and
`WorldwiseDeletion m Concrete` (every world).

*Origin-compatible deletion* is a world-inventory (recombination) principle, not
an origin principle: for every world `v` and concrete individual `x` existing
there, some world lacks `x` while every individual it shares with `v` has near
origins in the two worlds. Its extreme case is a world with no individuals.
It is an explicit candidate commitment; the origin-tolerance account encoded in
`OriginToleranceIdentity` neither contains nor excludes it.

`Control.withEmpty` adds a world with no individuals to the encoded
origin-tolerance countermodel; `Control.Certificate` records what holds there and
in the two earlier models.
-/

@[expose] public section

namespace TruthCore.Causality.OriginDeletion

open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Causality.OriginToleranceIdentity

variable {W B O : Type}

/-- Every concrete individual existing at `w` is absent from some world
accessible from `w`. -/
def DeletionAt (m : Ontic W B) (Concrete : B → Prop) (w : W) : Prop :=
  ∀ x, Concrete x → m.ExistsAt w x → ∃ u, m.frame.access w u ∧ ¬ m.ExistsAt u x

/-- Deletion holds at every world accessible from `w`. -/
def AccessibleDeletion (m : Ontic W B) (Concrete : B → Prop) (w : W) : Prop :=
  ∀ v, m.frame.access w v → DeletionAt m Concrete v

/-- Deletion fails at some world accessible from `w`. -/
def NoAccessibleDeletion (m : Ontic W B) (Concrete : B → Prop) (w : W) : Prop :=
  ¬ AccessibleDeletion m Concrete w

/-- Deletion holds at every world. -/
def WorldwiseDeletion (m : Ontic W B) (Concrete : B → Prop) : Prop :=
  ∀ v, DeletionAt m Concrete v

/-- For each world `v` and concrete individual `x` existing at `v`, some world
lacks `x` and gives every individual it shares with `v` an origin near its
origin at `v`. A claim about which worlds there are; it does not mention access. -/
def OriginCompatibleDeletion (m : Ontic W B) (Concrete : B → Prop)
    (I : OriginInterface W B O) : Prop :=
  ∀ v x, Concrete x → m.ExistsAt v x → ∃ u, ¬ m.ExistsAt u x ∧
    ∀ y, m.ExistsAt v y → m.ExistsAt u y → I.near (I.origin v y) (I.origin u y)

/-- Some world has no existing individual at all, concrete or not. A world
merely lacking every concrete individual is weaker: origin-determined access
also checks shared non-concrete individuals. -/
def EmptyWorld (m : Ontic W B) : Prop :=
  ∃ e, ∀ x, ¬ m.ExistsAt e x

namespace Control

open TruthCore.Causality.ToleranceOriginRival.Control (Origin tolerance)

/-- The five worlds of `OriginToleranceIdentity.Control.faithful` and a sixth,
`empty`, at which no individual exists. -/
inductive World where
  | aMinus | actual | plus | bMinus | bPlus | empty
  deriving DecidableEq

def exists' : World → Bool → Prop
  | World.aMinus, x => x = false
  | World.actual, _ => True
  | World.plus, _ => True
  | World.bMinus, x => x = true
  | World.bPlus, x => x = true
  | World.empty, _ => False

/-- As in `faithful`; the origin at `empty` is idle. -/
def originOf : World → Bool → Origin
  | World.aMinus, _ => Origin.minus
  | World.actual, _ => Origin.actual
  | World.plus, false => Origin.plus
  | World.plus, true => Origin.actual
  | World.bMinus, _ => Origin.minus
  | World.bPlus, _ => Origin.plus
  | World.empty, _ => Origin.actual

def interface : OriginInterface World Bool Origin := ⟨tolerance.access, originOf⟩

/-- Access fails exactly where it fails in `faithful`; `empty` accesses and is
accessed by every world. -/
def far : World → World → Prop
  | World.aMinus, World.plus => True
  | World.plus, World.aMinus => True
  | World.bMinus, World.bPlus => True
  | World.bPlus, World.bMinus => True
  | _, _ => False

def withEmpty : Ontic World Bool :=
  { frame := ⟨fun u v => ¬ far u v⟩, ExistsAt := exists', Causes := fun _ _ _ => False }

/-- (1) In `faithful`, every individual counted concrete: deletion holds at
`actual`, fails at `plus`, and fails at some world accessible from `actual`.
(2) In `restored`, deletion fails at the actual offset. (3) In `withEmpty`: the
four encoded origin commitments, origin-compatible deletion and worldwise
deletion hold. -/
def Certificate : Prop :=
  (DeletionAt OriginToleranceIdentity.Control.faithful.ontic (fun _ => True)
      OriginToleranceIdentity.Control.World.actual ∧
    ¬ DeletionAt OriginToleranceIdentity.Control.faithful.ontic (fun _ => True)
      OriginToleranceIdentity.Control.World.plus ∧
    NoAccessibleDeletion OriginToleranceIdentity.Control.faithful.ontic (fun _ => True)
      OriginToleranceIdentity.Control.World.actual) ∧
  ¬ DeletionAt OriginToleranceIdentity.Control.restored (fun _ => True) Origin.actual ∧
  (NearIsTolerance interface ∧ OriginDeterminesAccess withEmpty interface ∧
    OriginPlenitude withEmpty (fun _ => True) interface ∧
    VariedOriginAt withEmpty (fun _ => True) interface World.actual ∧
    OriginCompatibleDeletion withEmpty (fun _ => True) interface ∧
    WorldwiseDeletion withEmpty (fun _ => True))

end Control

end TruthCore.Causality.OriginDeletion
