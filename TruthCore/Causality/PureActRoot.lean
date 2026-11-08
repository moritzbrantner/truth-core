module

public import TruthCore.Causality.PureActThisness
public import TruthCore.Causality.PureIndiscernibility
public import TruthCore.Causality.NecessaryRootUniqueness
public import TruthCore.Causality.WholeRosterFoundation

/-! Pure-act premises at the actual roots of the necessary-root route (#320)

Analyst formulation, attribution deferred.

The pure-act uniqueness theorems (`PureActThisness`, `PureIndiscernibility`)
quantify over first unmoved movers. The necessary-root route
(`NecessaryRootUniqueness`) reaches one actual concrete root of a selected
grounding relation that is necessary at accessible worlds, and gets its
uniqueness from a maximum in being (grades, the genus principle, the has-being
and necessity-cause bridges). This module restates unrestricted perfection,
strict pure actuality and real thisness for the *actual roots* of that same
grounding relation, so that they can replace the maximum bundle as the
uniqueness half of the route.

Being an actual root (actually concrete and actually grounded by no actual
concretum) is a different property from being a first unmoved mover (moving
something and moved in no respect). The root-indexed premises below are
therefore new statements, not instances of the first-mover ones. The re-indexing
`rootMoved`/`rootMoves` only shows that the pure-act argument uses nothing about
motion: it reads "unmoved" as "is an actual root" and "moves" as "is an actual
root", so that first-mover status coincides with actual rootness
(`firstIffRoot`), and the earlier theorems then apply unchanged. No causal or
motion claim about roots is made by that re-indexing. -/

@[expose] public section

namespace TruthCore.Causality.PureActRoot
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessaryRootFork (ActualRoot)
open TruthCore.Case.Catholicism

variable {W B D : Type}

/-- Unrestricted perfection at the actual roots: every actual root of the
selected grounding relation at `w` really has every pure perfection. -/
def ActualRootHasEveryPureDetermination (m : Profile W B) (w : W)
    (Has : B → D → Prop) (Pure : D → Prop) : Prop :=
  ∀ r, ActualRoot m w r → ∀ d, Pure d → Has r d

/-- Strict pure actuality at the actual roots: each real determination of an
actual root is a pure perfection. -/
def ActualRootDeterminationsArePure (m : Profile W B) (w : W)
    (Has : B → D → Prop) (Pure : D → Prop) : Prop :=
  ∀ r, ActualRoot m w r → ∀ d, Has r d → Pure d

/-- Real thisness at the actual roots: each actual root has a real determination
that no other being has. -/
def ActualRootHasRealThisness (m : Profile W B) (w : W) (Has : B → D → Prop) : Prop :=
  ∀ r, ActualRoot m w r → ∃ d, Has r d ∧ ∀ y, Has y d → y = r

/-- Re-indexing only: a being counts as "moved" exactly when it is not an actual
root. No motion or causation is asserted. -/
def rootMoved (m : Profile W B) (w : W) (x : B) (_ : Unit) : Prop := ¬ ActualRoot m w x

/-- Re-indexing only: an actual root counts as "moving" something (itself). -/
def rootMoves (m : Profile W B) (w : W) (f : B) (_ : B) (_ : Unit) : Prop := ActualRoot m w f

namespace Control
open TruthCore.Causality.NecessaryConcreteRouteBridge (oneWorld)
open TruthCore.Causality.NecessaryRootUniqueness (UniqueNecessaryActualRootAt)
open TruthCore.Causality.WholeRosterFoundation (WholeRosterNotTrapped)
open TruthCore.Causality.BruteFoundationBoundary (EveryContingentGroundedAt)
open TruthCore.Causality.PureIndiscernibility (PurelyDeterminedIndiscerniblesIdentical)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)

/-- One world, two concrete candidates, no grounding: both are actual roots. -/
def twoRoots : Profile Unit Bool := oneWorld (fun _ _ => False)

/-- One world, `true` grounds `false`: `true` is the only actual root. -/
def oneRoot : Profile Unit Bool := oneWorld (fun y x => y = true ∧ x = false)

/-- One world with no candidates at all. -/
def empty : Profile Unit Empty :=
  { ontic := { frame := { access := fun _ _ => True }, ExistsAt := fun _ _ => True,
               Causes := fun _ _ _ => False }
    concrete := fun _ => True  -- category-constant: intended (empty carrier; the model tests only the population premise)
    grounds := fun _ _ _ => False }

/-- No real distinction: every being has the one determination. -/
def sameHas (_ : Bool) (_ : Unit) : Prop := True

/-- One shared act respect plus a thisness `Sum.inr b` for each candidate `b`. -/
def thisHas (x : Bool) : Unit ⊕ Bool → Prop :=
  Sum.rec (motive := fun _ => Prop) (fun _ => True) (fun b => x = b)

/-- Only the shared act respect is pure; the thisnesses are individuating
principles. -/
def actOnly : Unit ⊕ Bool → Prop :=
  Sum.rec (motive := fun _ => Prop) (fun _ => True) (fun _ => False)

/-- Only `true` has the one determination. -/
def onlyTrue (x : Bool) (_ : Unit) : Prop := x = true

/-- The four non-logical existence-side premises of the route at `()`. -/
def Background {B : Type} (m : Profile Unit B) : Prop :=
  InhabitedConcreteAt m.ontic m.concrete () ∧ WholeRosterNotTrapped m () ∧
    EveryContingentGroundedAt m ()

/-- Finite interpretations only: satisfiability of the encoded bundles, not
metaphysical possibility. Excluded middle is a premise of the route and is not
asserted here; every listed model satisfies its other premises outright.
* Bare roots: two actual necessary roots with the same determinations satisfy
  the existence-side background, unrestricted perfection and strict pure
  actuality; real thisness, the narrower bridge and uniqueness fail.
* Strict pure actuality omitted: non-pure thisnesses keep unrestricted
  perfection, real thisness and the (vacuous) narrower bridge; uniqueness fails.
* Unrestricted perfection omitted: the same thisnesses counted pure keep strict
  pure actuality, real thisness and the narrower bridge; uniqueness fails.
* Population omitted: on an empty carrier whole-roster nontrapping, contingent
  dependence and all three root premises hold vacuously; uniqueness fails.
* Positive witness: with one actual root, every non-logical premise of both
  routes holds and so does the conclusion. -/
def Certificate : Prop :=
  (Background twoRoots ∧
    ActualRootHasEveryPureDetermination twoRoots () sameHas (fun _ => True) ∧
    ActualRootDeterminationsArePure twoRoots () sameHas (fun _ => True) ∧
    ¬ ActualRootHasRealThisness twoRoots () sameHas ∧
    ¬ PurelyDeterminedIndiscerniblesIdentical sameHas (fun _ => True) ∧
    ¬ UniqueNecessaryActualRootAt twoRoots ()) ∧
  (Background twoRoots ∧
    ActualRootHasEveryPureDetermination twoRoots () thisHas actOnly ∧
    ¬ ActualRootDeterminationsArePure twoRoots () thisHas actOnly ∧
    ActualRootHasRealThisness twoRoots () thisHas ∧
    PurelyDeterminedIndiscerniblesIdentical thisHas actOnly ∧
    ¬ UniqueNecessaryActualRootAt twoRoots ()) ∧
  (Background twoRoots ∧
    ¬ ActualRootHasEveryPureDetermination twoRoots () thisHas (fun _ => True) ∧
    ActualRootDeterminationsArePure twoRoots () thisHas (fun _ => True) ∧
    ActualRootHasRealThisness twoRoots () thisHas ∧
    PurelyDeterminedIndiscerniblesIdentical thisHas (fun _ => True) ∧
    ¬ UniqueNecessaryActualRootAt twoRoots ()) ∧
  (¬ InhabitedConcreteAt empty.ontic empty.concrete () ∧
    WholeRosterNotTrapped empty () ∧ EveryContingentGroundedAt empty () ∧
    ActualRootHasEveryPureDetermination empty () (fun _ (_ : Unit) => True) (fun _ => True) ∧
    ActualRootDeterminationsArePure empty () (fun _ (_ : Unit) => True) (fun _ => True) ∧
    ActualRootHasRealThisness empty () (fun _ (_ : Unit) => True) ∧
    PurelyDeterminedIndiscerniblesIdentical (fun (_ : Empty) (_ : Unit) => True) (fun _ => True) ∧
    ¬ UniqueNecessaryActualRootAt empty ()) ∧
  (Background oneRoot ∧
    ActualRootHasEveryPureDetermination oneRoot () onlyTrue (fun _ => True) ∧
    ActualRootDeterminationsArePure oneRoot () onlyTrue (fun _ => True) ∧
    ActualRootHasRealThisness oneRoot () onlyTrue ∧
    PurelyDeterminedIndiscerniblesIdentical onlyTrue (fun _ => True) ∧
    UniqueNecessaryActualRootAt oneRoot ())

end Control
end TruthCore.Causality.PureActRoot
