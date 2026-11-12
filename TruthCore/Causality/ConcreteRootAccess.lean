module
public import TruthCore.Causality.ClosedGroundingRoots

/-! Finite access at one fixed profile/world/relation. Analyst definitions;
attribution deferred. These decompose CCR and supply no independent warrant. -/
@[expose] public section
namespace TruthCore.Causality.ConcreteRootAccess
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.CogitoNecessaryConcrete (ActualConcreteGround)
open TruthCore.Causality.NecessaryRootFork
open TruthCore.Causality.ClosedGroundingRoots
variable {W B : Type}

/-- Finite supplier-to-recipient path, starting at an actual concrete root.
Every endpoint is actual concrete; the zero-edge root path is admitted. -/
inductive RootAccess (m : Profile W B) (w : W) : B → Prop
  | root {x} : ActualRoot m w x → RootAccess m w x
  | step {y x} : RootAccess m w y → ActualConcrete m w x →
      ActualConcreteGround m w y x → RootAccess m w x

def UniversalRootAccess (m : Profile W B) (w : W) : Prop :=
  ∀ x, ActualConcrete m w x → RootAccess m w x

/-- Root access is demanded only for concrete recipients with an actual
nonconcrete supplier. This permits partial abstract co-grounds. -/
def LocalizedBridge (m : Profile W B) (w : W) : Prop :=
  ∀ x y, ActualConcrete m w x → m.ontic.ExistsAt w y →
    ¬ m.concrete y → m.grounds w y x → RootAccess m w x

def RootAccessEquivalence (m : Profile W B) (w : W) : Prop :=
  ClosedGroundingCollectionsRooted m w ↔ UniversalRootAccess m w

def BorrowedDecomposition (m : Profile W B) (w : W) : Prop :=
  ClosedGroundingCollectionsRooted m w ↔
    NoWhollyBorrowedCollection m w ∧ LocalizedBridge m w

def BlanketEquivalence (m : Profile W B) (w : W) : Prop :=
  ClosedGroundingCollectionsRooted m w ↔ NoWhollyBorrowedCollection m w
end TruthCore.Causality.ConcreteRootAccess
