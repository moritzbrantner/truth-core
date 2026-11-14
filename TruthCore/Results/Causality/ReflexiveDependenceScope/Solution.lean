module

public import Mathlib.Data.Fintype.Basic
public import TruthCore.Causality.ReflexiveDependenceScope
public import TruthCore.Causality.StrictPriorityPureAct
public import TruthCore.Alternatives.ActPotencyRegress

@[expose] public section

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
  rintro ⟨b⟩ hAsym
  exact hAsym b b (hRefl b) (hRefl b)

/-- Two finite models separate reflexive, distinct-nonmutual dependence from
asymmetric dependence. -/
theorem separationModels : Control.ReflexiveDistinctSeparation := by
  unfold Control.ReflexiveDistinctSeparation DependenceForBeingReflexive
    DependenceForBeingTransitive DistinctBeingsNotMutuallyDependent
    DependenceForBeingAsymmetric
    TruthCore.Causality.DependenceStrictGroundMapStrength.DistinctEdge
  beta_reduce
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- Under the two OPEN priority bridges, transitivity of dependence for being
makes simple priority transitive. -/
theorem priorityTransitiveFromDependence {B : Type} (PriorSimply D : B → B → Prop)
    (hSuff : NonmutualDependenceSufficesForPriority PriorSimply D)
    (hReq : PriorityRequiresNonmutualDependence PriorSimply D)
    (hTrans : DependenceForBeingTransitive D) :
    SimplePriorityTransitiveReading PriorSimply := by
  intro x y z hxy hyz
  obtain ⟨hDyx, hNxy⟩ := hReq x y hxy
  obtain ⟨hDzy, _⟩ := hReq y z hyz
  refine hSuff x z (hTrans z y x hDzy hDyx) ?_
  intro hDxz
  exact hNxy (hTrans x z y hDxz hDzy)

/-- The requirement half of the priority bridge alone makes simple priority
irreflexive: `PriorSimply x x` would need both `D x x` and `¬ D x x`. -/
theorem priorityIrreflexiveFromRequirement {B : Type} (PriorSimply D : B → B → Prop)
    (hReq : PriorityRequiresNonmutualDependence PriorSimply D) :
    StrictSimplePriority PriorSimply :=
  ⟨fun x h => (hReq x x h).2 (hReq x x h).1⟩

/-- Asymmetry of actual grounding without asymmetry of dependence: the distinct
case uses distinct nonmutuality, and the self case a separate irreflexivity
premise about grounding itself. -/
theorem actualGroundingAsymmetricViaDistinct {W B : Type} (m : Profile W B) (w : W)
    (D : B → B → Prop)
    (hDep : ActualGroundingIsDependence m w D)
    (hDistinct : DistinctBeingsNotMutuallyDependent D)
    (hIrrefl : ActualGroundingIrreflexive m w) :
    ActualGroundingAsymmetric m w := by
  intro a b ha hb hab hba
  by_cases h : a = b
  · subst h
    exact hIrrefl a ha hab
  · exact hDistinct b a (fun e => h e.symm) (hDep a b ha hb hab) (hDep b a hb ha hba)

/-- With reflexive dependence, the unrestricted dependence-to-grounding bridge
makes every actual concretum ground itself. -/
theorem reflexiveDependenceForcesSelfGrounding {W B : Type} (m : Profile W B) (w : W)
    (D : B → B → Prop)
    (hRefl : DependenceForBeingReflexive D)
    (hDep : ActualDependenceIsGrounding m w D) :
    EveryActualConcretumGroundsItself m w :=
  fun a ha => hDep a a ha ha (hRefl a)

/-- The unrestricted dependence-to-grounding bridge implies its restriction to
distinct relata. -/
theorem distinctDependenceGroundingFromUnrestricted {W B : Type} (m : Profile W B)
    (w : W) (D : B → B → Prop)
    (hDep : ActualDependenceIsGrounding m w D) :
    ActualDistinctDependenceIsGrounding m w D :=
  fun c x _ hx hc h => hDep c x hx hc h

/-- Order-law controls: transitivity of priority is not supplied by the
bridges, and a reciprocal pair has no strict part. -/
theorem orderLawControls : Control.OrderLawControls := by
  unfold Control.OrderLawControls DependenceForBeingReflexive
    DependenceForBeingTransitive DistinctBeingsNotMutuallyDependent
    NonmutualDependenceSufficesForPriority PriorityRequiresNonmutualDependence
    Control.chainPrior Control.chainD Control.pairD
  refine ⟨⟨?_, ?_, fun _ _ h1 h2 => ⟨h1, h2⟩, fun _ _ h => h, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;>
    decide

end TruthCore.Results.Causality.ReflexiveDependenceScope
