import TruthCore.Causality.NecessarySupportCoverage
import TruthCore.Causality.NecessaryConcreteRouteBridge
import TruthCore.Results.Causality.SpineRivalsRootEsse.Solution

namespace TruthCore.Results.Causality.NecessarySupportCoverage

open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryRootFork
open TruthCore.Causality.NecessarilyUnderived
open TruthCore.Causality.NecessaryConcreteUnderived
open TruthCore.Causality.NecessaryConcreteRouteBridge (necessaryActualRootOfGrounded)
open TruthCore.Causality.SpineRivalsRootEsse
open TruthCore.Causality.NecessarySupportCoverage
open TruthCore.Causality.NecessarySupportCoverage.Control
open TruthCore.German.Kant.CosmologicalInference (Ontic NecessaryAt ContingentAt)
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)

/-- J2 derived. Reflexive access at `w`, well-founded present concrete grounding
at `w` (both already premises of the join) and the existing one-way no-novel-edge
condition on the concrete subtype give a well-founded cross-world union of support
among necessary concreta. Composes `union_wellFounded_of_actual_wellFounded`. -/
theorem unionWFOfNoNovel (m : Profile W B) (w : W)
    (hRef : ActualReflexive m.ontic w) (hWF : ActualGroundingWF m w)
    (hNoNovel : NoNovelNecessarySupport (concreteOntic m) (concreteSupport m) w) :
    ConcreteNecessaryUnionWF m w := by
  sorry

/-- The mutual-support rival is excluded by reflexive access at `w`, well-founded
present grounding at `w` and the one-way no-novel-edge condition. -/
theorem mutualSupportExcluded (m : Profile W B) (w : W)
    (hRef : ActualReflexive m.ontic w) (hWF : ActualGroundingWF m w)
    (hNoNovel : NoNovelNecessarySupport (concreteOntic m) (concreteSupport m) w) :
    NoNecessaryConcretaMutualSupport m w := by
  sorry

/-- The join's endpoint without J1, J2 or reflexive access. The actual necessary
root (`necessaryActualRootOfGrounded`) has no concrete ground at `w`; coverage
transfers that to every admitted world. The witness is that root itself. -/
theorem underivedOfCoverage (m : Profile W B) (w : W)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w) (hWF : ActualGroundingWF m w)
    (hDep : EveryContingentGroundedAt m w) (hEM : ExcludedMiddle)
    (hCov : NecessarySupportActuallyCovered m w) :
    NecessaryConcreteUnderivedAt m w := by
  sorry

/-- The stage-one form of the join without J2 or reflexive access: from a
necessary concretum, well-founded present grounding at `w`, J1 and coverage.
Descend present grounding among actual necessary concreta. A supporter of such a
concretum at any admitted world yields, by coverage, a present concrete supporter
at `w`, which J1 (used only at `w`) makes necessary and which is lower; so a minimal
one has no existing concrete supporter at any admitted world. Constructive core,
then excluded middle. The witness may differ from the given one. -/
theorem underivedFromNecessityOfCoverage (m : Profile W B) (w : W)
    (hNecessary : NecessaryConcreteAt m w) (hWF : ActualGroundingWF m w)
    (hNoCont : NoContingentConcreteSupport m w)
    (hCov : NecessarySupportActuallyCovered m w) (hEM : ExcludedMiddle) :
    NecessaryConcreteUnderivedAt m w := by
  sorry

/-- Coverage is implied by reflexive access, J1 (no contingent concrete support)
and the one-way no-novel-edge condition: the supporter elsewhere is necessary, so
it exists at `w`, and its edge already occurs at `w`. -/
theorem coverageOfNoContingentNoNovel (m : Profile W B) (w : W)
    (hRef : ActualReflexive m.ontic w) (hNoCont : NoContingentConcreteSupport m w)
    (hNoNovel : NoNovelNecessarySupport (concreteOntic m) (concreteSupport m) w) :
    NecessarySupportActuallyCovered m w := by
  sorry

/-- Coverage is implied by the existing same-supporter presence premise: the
supporter found elsewhere is itself present and supporting at `w`. -/
theorem coverageOfSupportIsPresent (m : Profile W B) (w : W)
    (hPresent : TruthCore.Causality.UnderivedRootRoute.NecessarySupportIsPresent m w) :
    NecessarySupportActuallyCovered m w := by
  sorry

/-! ## Controls -/

/-- All three controls hold. -/
theorem controls : Controls := by
  sorry

end TruthCore.Results.Causality.NecessarySupportCoverage
