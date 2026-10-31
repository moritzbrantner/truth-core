import TruthCore.Causality.UnderivedRootRoute

namespace TruthCore.Results.Causality.UnderivedRootRoute

open TruthCore.Causality.BruteFoundationBoundary (Profile EveryContingentGroundedAt)
open TruthCore.Causality.NecessarilyUnderived (NecessarilyUnderived)
open TruthCore.Causality.NecessaryRootFork (ActualGroundingWF)
open TruthCore.Causality.UnderivedRootRoute
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)

/-- The whole route: an inhabited world with well-founded restricted grounding, the closing
premise, present support and concrete supporters has a necessarily underived individual. -/
theorem necessarilyUnderivedOfGrounded {W B : Type} (m : Profile W B) (w : W)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w) (hWF : ActualGroundingWF m w)
    (hDep : EveryContingentGroundedAt m w) (hEM : ExcludedMiddle)
    (hPresent : NecessarySupportIsPresent m w) (hConcrete : ActualSupportersConcrete m w) :
    NecessarilyUnderived m.ontic m.grounds w := by
  sorry

/-- Coverage: an inhabited world has a necessarily underived individual, or takes one of the
four exits. Not exclusive. -/
theorem underivedRouteExit {W B : Type} (m : Profile W B) (w : W)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w) (hEM : ExcludedMiddle) :
    UnderivedRouteExit m w := by
  sorry

/-- The control bundle of `UnderivedRouteControls`. -/
theorem underivedRouteControls : UnderivedRouteControls := by
  sorry

end TruthCore.Results.Causality.UnderivedRootRoute
