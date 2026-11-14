import Mathlib.Data.Fintype.Basic
import TruthCore.Causality.ReflexiveDependenceScope
import TruthCore.Causality.StrictPriorityPureAct
import TruthCore.Alternatives.ActPotencyRegress

namespace TruthCore.Results.Causality.ReflexiveDependenceScope

open TruthCore.Causality.ReflexiveDependenceScope
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessaryRootFork (ActualConcrete)
open TruthCore.Causality.NecessaryConcreteRouteBridge (ActualGroundingAsymmetric)
open TruthCore.Causality.Round2Grounding
open TruthCore.Causality.Round2PerfectionPrimacy (DistinctBeingsNotMutuallyDependent)
open TruthCore.Causality.CausalMapsBatch1
  (NonmutualDependenceSufficesForPriority PriorityRequiresNonmutualDependence)
open TruthCore.Causality.StrictPriorityPureAct (StrictSimplePriority)
open TruthCore.Alternatives.ActPotencyRegress (SimplePriorityTransitiveReading)

/-- Reflexive dependence for being is not asymmetric on any inhabited domain:
one being `b` with `D b b` is already a mutual pair. -/
theorem reflexiveRefutesAsymmetry {B : Type} (D : B → B → Prop)
    (hRefl : DependenceForBeingReflexive D) :
    InhabitedDependenceNotAsymmetric D := by
  sorry

/-- Two finite models separate reflexive, distinct-nonmutual dependence from
asymmetric dependence. -/
theorem separationModels : Control.ReflexiveDistinctSeparation := by
  sorry

/-- Under the two OPEN priority bridges, transitivity of dependence for being
makes simple priority transitive. -/
theorem priorityTransitiveFromDependence {B : Type} (PriorSimply D : B → B → Prop)
    (hSuff : NonmutualDependenceSufficesForPriority PriorSimply D)
    (hReq : PriorityRequiresNonmutualDependence PriorSimply D)
    (hTrans : DependenceForBeingTransitive D) :
    SimplePriorityTransitiveReading PriorSimply := by
  sorry

/-- The requirement half of the priority bridge alone makes simple priority
irreflexive: `PriorSimply x x` would need both `D x x` and `¬ D x x`. -/
theorem priorityIrreflexiveFromRequirement {B : Type} (PriorSimply D : B → B → Prop)
    (hReq : PriorityRequiresNonmutualDependence PriorSimply D) :
    StrictSimplePriority PriorSimply := by
  sorry

/-- Asymmetry of actual grounding without asymmetry of dependence: the distinct
case uses distinct nonmutuality, and the self case a separate irreflexivity
premise about grounding itself. -/
theorem actualGroundingAsymmetricViaDistinct {W B : Type} (m : Profile W B) (w : W)
    (D : B → B → Prop)
    (hDep : ActualGroundingIsDependence m w D)
    (hDistinct : DistinctBeingsNotMutuallyDependent D)
    (hIrrefl : ActualGroundingIrreflexive m w) :
    ActualGroundingAsymmetric m w := by
  sorry

/-- With reflexive dependence, the unrestricted dependence-to-grounding bridge
makes every actual concretum ground itself. -/
theorem reflexiveDependenceForcesSelfGrounding {W B : Type} (m : Profile W B) (w : W)
    (D : B → B → Prop)
    (hRefl : DependenceForBeingReflexive D)
    (hDep : ActualDependenceIsGrounding m w D) :
    EveryActualConcretumGroundsItself m w := by
  sorry

/-- The unrestricted dependence-to-grounding bridge implies its restriction to
distinct relata. -/
theorem distinctDependenceGroundingFromUnrestricted {W B : Type} (m : Profile W B)
    (w : W) (D : B → B → Prop)
    (hDep : ActualDependenceIsGrounding m w D) :
    ActualDistinctDependenceIsGrounding m w D := by
  sorry

/-- Order-law controls: transitivity of priority is not supplied by the
bridges, and a reciprocal pair has no strict part. -/
theorem orderLawControls : Control.OrderLawControls := by
  sorry

end TruthCore.Results.Causality.ReflexiveDependenceScope
