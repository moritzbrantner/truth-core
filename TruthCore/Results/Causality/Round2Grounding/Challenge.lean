import TruthCore.Causality.Round2Grounding

namespace TruthCore.Results.Causality.Round2Grounding
open TruthCore.Causality.Round2Grounding
open TruthCore.Causality.BruteFoundationBoundary (Profile EveryContingentGroundedAt)
open TruthCore.Causality.NecessaryRootFork (ActualConcrete ActualGroundingWF)
open TruthCore.Causality.NecessaryConcreteRouteBridge
open TruthCore.Causality.MaximalGroundingAsymmetry (AtMaximalTarget)
open TruthCore.Causality.CausalMapsBatch1 (PriorityRequiresNonmutualDependence)
open TruthCore.Causality.GodMaximalCausal (MoreInIsAsymmetric)
open TruthCore.Case.Catholicism (SimplyPriorIsCauseOfBeing)
open TruthCore.German.Kant.CosmologicalInference (LocalCausalPrinciple)
open TruthCore.Latin.Aquinas.SummaTheologiae (IsMaximumIn)

/-- Map 2 (esse cause). A distinct cause of the esse of an actual concretum is
concrete (causal-capacity reading), exists at `w` (only actual things cause),
and the effect depends on it, so by the dependence bridge it grounds the effect. -/
theorem esseCauseGroundViaDependence {W B R : Type} (m : Profile W B) (w : W)
    (CausesIn : B → B → R → Prop) (esse : R) (DependsForBeing : B → B → Prop)
    (hExists : EsseCausesExistAt m w CausesIn esse)
    (hConcrete : EsseCausesAreConcrete m CausesIn esse)
    (hDep : EsseEffectDependsOnItsCause CausesIn esse DependsForBeing)
    (hGround : ActualDependenceIsGrounding m w DependsForBeing) :
    EsseCauseIsActualConcreteGround m w CausesIn esse := by
  sorry

/-- Map 3 (simply prior), dependence route. The simply prior is depended on by
what is posterior to it; both are actual concreta; dependence between actual
concreta is grounding. -/
theorem simplyPriorGroundViaDependence {W B : Type} (m : Profile W B) (w : W)
    (PriorSimply DependsForBeing : B → B → Prop)
    (hReq : PriorityRequiresNonmutualDependence PriorSimply DependsForBeing)
    (hRel : SimplePriorityRelatesActualConcreta m w PriorSimply)
    (hGround : ActualDependenceIsGrounding m w DependsForBeing) :
    SimplyPriorIsActualConcreteGround m w PriorSimply := by
  sorry

/-- Map 3 (simply prior), esse-cause route: composes the stage-one premise that
the simply prior causes the esse of what is posterior with the esse-cause bridge. -/
theorem simplyPriorGroundViaEsseCause {W B R : Type} (m : Profile W B) (w : W)
    (PriorSimply : B → B → Prop) (CausesIn : B → B → R → Prop) (esse : R)
    (hCause : SimplyPriorIsCauseOfBeing PriorSimply CausesIn esse)
    (hRel : SimplePriorityRelatesActualConcreta m w PriorSimply)
    (hEsse : EsseCauseIsActualConcreteGround m w CausesIn esse) :
    SimplyPriorIsActualConcreteGround m w PriorSimply := by
  sorry

/-- Map 4 (necessity causes), esse-cause route. -/
theorem necessityCauseGroundViaEsseCause {W B R : Type} (m : Profile W B) (w : W)
    (CausesNecessityOf : B → B → Prop) (CausesIn : B → B → R → Prop) (esse : R)
    (hCause : NecessityCauseCausesEsse CausesNecessityOf CausesIn esse)
    (hRel : NecessityCauseRelataActualConcrete m w CausesNecessityOf)
    (hEsse : EsseCauseIsActualConcreteGround m w CausesIn esse) :
    NecessityCausesAreActualConcreteGrounds m w CausesNecessityOf := by
  sorry

/-- Map 4 (necessity causes), dependence route. -/
theorem necessityCauseGroundViaDependence {W B : Type} (m : Profile W B) (w : W)
    (CausesNecessityOf DependsForBeing : B → B → Prop)
    (hDep : NecessitatedDependsOnItsCause CausesNecessityOf DependsForBeing)
    (hRel : NecessityCauseRelataActualConcrete m w CausesNecessityOf)
    (hGround : ActualDependenceIsGrounding m w DependsForBeing) :
    NecessityCausesAreActualConcreteGrounds m w CausesNecessityOf := by
  sorry

/-- Map 1 (contingent grounded), participation route: an actual contingent
concretum has participated esse, so a distinct cause of its esse, which by the
esse-cause bridge is an actual concrete ground. -/
theorem contingentGroundedViaParticipation {W B R : Type} (m : Profile W B) (w : W)
    (Participates : B → Prop) (CausesIn : B → B → R → Prop) (esse : R)
    (hPart : ContingentConcretumParticipatesEsse m w Participates)
    (hCause : ParticipatedEsseHasDistinctCause Participates CausesIn esse)
    (hEsse : EsseCauseIsActualConcreteGround m w CausesIn esse) :
    EveryContingentGroundedAt m w := by
  sorry

/-- Map 1, Kantian local-cause route: the local causal principle supplies an
existing distinct cause, which the bridge makes a concrete ground. -/
theorem contingentGroundedViaLocalCause {W B : Type} (m : Profile W B) (w : W)
    (hLocal : LocalCausalPrinciple m.ontic)
    (hBridge : ExistingCauseOfActualConcretumIsConcreteGround m w) :
    EveryContingentGroundedAt m w := by
  sorry

/-- Map 1, dependence route. -/
theorem contingentGroundedViaDependence {W B : Type} (m : Profile W B) (w : W)
    (DependsForBeing : B → B → Prop)
    (hDep : ActualContingentDependsOnActualConcretum m w DependsForBeing)
    (hGround : ActualDependenceIsGrounding m w DependsForBeing) :
    EveryContingentGroundedAt m w := by
  sorry

/-- Map 5 (asymmetry): restricted well-foundedness gives asymmetry. Reuses
`actualGroundingAsymmetricOfWF`. -/
theorem asymmetricFromWF {W B : Type} (m : Profile W B) (w : W)
    (hWF : ActualGroundingWF m w) : ActualGroundingAsymmetric m w := by
  sorry

/-- Map 5, priority route: a reciprocal pair would make each simply prior to the
other, so each would depend and not depend on the other. -/
theorem asymmetricViaPriority {W B : Type} (m : Profile W B) (w : W)
    (PriorSimply DependsForBeing : B → B → Prop)
    (hPrior : ActualGroundingIsSimplePriority m w PriorSimply)
    (hReq : PriorityRequiresNonmutualDependence PriorSimply DependsForBeing) :
    ActualGroundingAsymmetric m w := by
  sorry

/-- Map 5, dependence route. -/
theorem asymmetricViaDependence {W B : Type} (m : Profile W B) (w : W)
    (DependsForBeing : B → B → Prop)
    (hDep : ActualGroundingIsDependence m w DependsForBeing)
    (hAsym : DependenceForBeingAsymmetric DependsForBeing) :
    ActualGroundingAsymmetric m w := by
  sorry

/-- Map 5, grades route: a ground is more in esse than what it grounds, and
"more in" is asymmetric. -/
theorem asymmetricViaGrades {W B R : Type} (m : Profile W B) (w : W)
    (MoreIn : R → B → B → Prop) (esse : R)
    (hMore : ActualGroundIsMoreInEsse m w MoreIn esse)
    (hAsym : MoreInIsAsymmetric MoreIn) :
    ActualGroundingAsymmetric m w := by
  sorry

/-- Map 6 (maximal target), grades route: nothing actual grounds a maximum in
esse at all, since its ground would be more in esse than it. The `InAct` part of
maximality is unused. -/
theorem atMaximalTargetViaGrades {W B R : Type} (m : Profile W B) (w : W)
    (InAct : B → R → Prop) (MoreIn : R → B → B → Prop) (esse : R)
    (hMore : ActualGroundIsMoreInEsse m w MoreIn esse) :
    AtMaximalTarget m w InAct MoreIn esse := by
  sorry

/-! ## Controls -/

open TruthCore.Causality.CogitoNecessaryConcrete (ActualConcreteGround)
open TruthCore.German.Kant.CosmologicalInference (ContingentAt)

/-- The batch controls. -/
theorem controls : TruthCore.Causality.Round2Grounding.Control.Certificate := by
  sorry

end TruthCore.Results.Causality.Round2Grounding
