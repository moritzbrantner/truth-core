import TruthCore.Causality.ClosedGroundingRoots
import TruthCore.Results.Causality.NecessaryConcreteUnderived.Solution
import TruthCore.Results.Causality.NecessarySupportCoverage.Solution
import TruthCore.Results.Causality.QuantitativeTransferPaths.Solution

namespace TruthCore.Results.Causality.ClosedGroundingRoots

open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.CogitoNecessaryConcrete (ActualConcreteGround)
open TruthCore.Causality.NecessaryRootFork
open TruthCore.Causality.NecessarilyUnderived
open TruthCore.Causality.NecessaryConcreteUnderived
open TruthCore.Causality.NecessarySupportCoverage
open TruthCore.Causality.NecessarySupportActualScope
open TruthCore.Causality.NecessaryConcreteRouteBridge (NecessaryActualRootAt ActualGroundingAsymmetric)
open TruthCore.Causality.ClosedGroundingRoots
open TruthCore.Causality.ClosedGroundingRoots.Control
open TruthCore.Causality.QuantitativeTransferPaths (Path)
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt)
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)

/-- Well-founded actual grounding implies the closed-collection condition, with no
excluded middle: by well-founded induction no actual concretum belongs to a
ground-closed collection without a root. -/
theorem closedRootedOfWF {W B : Type} (m : Profile W B) (w : W)
    (hWF : ActualGroundingWF m w) : ClosedGroundingCollectionsRooted m w := by
  sorry

/-- A necessary concretum from the closed-collection condition: the AGWF-free
form of `NecessaryRootFork.necessaryConcreteOfActualGrounded`. -/
theorem necessaryConcreteOfClosedRooted {W B : Type} (m : Profile W B) (w : W)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w)
    (hC : ClosedGroundingCollectionsRooted m w)
    (hDep : EveryContingentGroundedAt m w) (hEM : ExcludedMiddle) :
    NecessaryConcreteAt m w := by
  sorry

/-- The join's endpoint from the actual necessary root and coverage, with the
closed-collection condition in place of AGWF. -/
theorem underivedOfCoverageClosed {W B : Type} (m : Profile W B) (w : W)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w)
    (hC : ClosedGroundingCollectionsRooted m w)
    (hDep : EveryContingentGroundedAt m w) (hEM : ExcludedMiddle)
    (hCov : NecessarySupportActuallyCovered m w) :
    NecessaryConcreteUnderivedAt m w := by
  sorry

/-- The join's endpoint from a necessary concretum, J1 and coverage, with the
closed-collection condition in place of AGWF: if no necessary concretum were
underived, the actual necessary concreta would form a nonempty collection, closed
under actual grounds by J1, with no root (by coverage a root would be underived). -/
theorem underivedFromNecessityOfCoverageClosed {W B : Type} (m : Profile W B) (w : W)
    (hNecessary : NecessaryConcreteAt m w)
    (hC : ClosedGroundingCollectionsRooted m w)
    (hNoCont : NoContingentConcreteSupport m w)
    (hCov : NecessarySupportActuallyCovered m w) (hEM : ExcludedMiddle) :
    NecessaryConcreteUnderivedAt m w := by
  sorry

/-- The same with the actual-world instance J1@w of J1. -/
theorem underivedFromNecessityOfActualCoverageClosed {W B : Type} (m : Profile W B) (w : W)
    (hNecessary : NecessaryConcreteAt m w)
    (hC : ClosedGroundingCollectionsRooted m w)
    (hAct : ActualNoContingentConcreteSupport m w)
    (hCov : NecessarySupportActuallyCovered m w) (hEM : ExcludedMiddle) :
    NecessaryConcreteUnderivedAt m w := by
  sorry

/-- The `checks` route of the join with the closed-collection condition in place
of AGWF: the necessary concretum comes from the closed-collection condition, the
rest is the existing modal union route. -/
theorem checksClosed {W B : Type} (m : Profile W B) (w : W)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w)
    (hC : ClosedGroundingCollectionsRooted m w)
    (hDep : EveryContingentGroundedAt m w)
    (hRef : ActualReflexive m.ontic w)
    (hNoCont : NoContingentConcreteSupport m w)
    (hUnion : ConcreteNecessaryUnionWF m w)
    (hEM : ExcludedMiddle) :
    NecessaryConcreteUnderivedAt m w := by
  sorry

/-- The per se attenuation bridge gives the closed-collection condition. The
network analogues `binaryFixed` and `halfFixed` show that `finitePath` fails
without uniform loss or without the common bound; no Profile-level control. From any
member of a ground-closed collection, the weighted-network theorem `finitePath`
finds a finite path of positive receptions to a thing with positive own esse;
each reception is an actual grounding edge, so the path stays inside the
collection, and its end is an actual root. -/
theorem closedRootedOfAttenuation {W B : Type} (m : Profile W B) (w : W)
    (h : AttenuatedEsseReception m w) : ClosedGroundingCollectionsRooted m w := by
  sorry

/-- The borrowed-reality principle over all modelled suppliers gives the
closed-collection condition, given that actual concreta are supplied only by
concreta: a ground-closed rootless collection is then closed under all actual
suppliers, and each member has one. -/
theorem closedRootedOfBorrowed {W B : Type} (m : Profile W B) (w : W)
    (hBR : NoWhollyBorrowedCollection m w)
    (hConc : ActualSuppliersOfConcretaConcrete m w) :
    ClosedGroundingCollectionsRooted m w := by
  sorry

/-! ## Controls -/

theorem controls : Controls := by
  sorry

end TruthCore.Results.Causality.ClosedGroundingRoots
