module

public import TruthCore.Causality.DependenceGroundingPriority
public import TruthCore.Logic.CogitoEsse
public import TruthCore.Results.Causality.EsseCausePriority.Solution
public import TruthCore.Results.Causality.ActPriorityThetaEight.Solution

@[expose] public section

namespace TruthCore.Results.Causality.DependenceGroundingPriority
open TruthCore.Causality.DependenceGroundingPriority
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessaryRootFork (ActualConcrete)
open TruthCore.Causality.NecessaryConcreteRouteBridge (EsseCauseIsActualConcreteGround
  SimplyPriorIsActualConcreteGround)
open TruthCore.Causality.Round2Grounding (ActualGroundingIsSimplePriority
  ActualDependenceIsGrounding EsseCausesExistAt EsseCausesAreConcrete
  EsseEffectDependsOnItsCause SimplePriorityRelatesActualConcreta)
open TruthCore.Causality.ReflexiveDependenceScope (ActualDistinctDependenceIsGrounding
  DependenceForBeingReflexive)
open TruthCore.Causality.CausalMapsBatch1 (PriorityRequiresNonmutualDependence)
open TruthCore.Causality.EsseCausePriority (ActualEsseCausePriority DistinctEsseCausePriority)
open TruthCore.Logic.CogitoEsse (EveryExistentConcreteAt)
open TruthCore.Causality.ActPriorityThetaEight
open TruthCore.Causality.ActPriorityAtFirst
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.InMetaphysicam

/-! ## The scoped route (#1590, step 1) -/

/-- Composition of the two OPEN bridges: a distinct actual concretum on which an
actual concretum depends for its being grounds it (distinct-relata bridge), and
actual grounding is simple priority. Plain conditional composition. -/
theorem actualDistinctDependencePriority {W B : Type} (m : Profile W B) (w : W)
    (D PriorSimply : B → B → Prop)
    (hGround : ActualDistinctDependenceIsGrounding m w D)
    (hPrior : ActualGroundingIsSimplePriority m w PriorSimply) :
    ActualDistinctDependencePriority m w D PriorSimply :=
  fun c x hne hx hc hD => hPrior c x hc hx (hGround c x hne hx hc hD)

/-- The scoped route gives the restriction of
`NonmutualDependenceSufficesForPriority` to actual concreta: the nonmutuality
antecedent already excludes `y = x`. It does not give the unscoped premise. -/
theorem actualNonmutualOfDistinct {W B : Type} (m : Profile W B) (w : W)
    (D PriorSimply : B → B → Prop)
    (hScoped : ActualDistinctDependencePriority m w D PriorSimply) :
    ActualNonmutualDependencePriority m w D PriorSimply := by
  intro y x hx hy hxy hyx
  refine hScoped y x ?_ hx hy hxy
  rintro rfl
  exact hyx hxy

/-! ## Root-connected application (#1590, step 2) -/

/-- The esse-cause priority node of #1604 through dependence: a distinct cause
`c` of the esse of an actual concretum `x` exists at `w` and is concrete, `x`
depends for its being on it, so by the scoped route `c` is simply prior to `x`. -/
theorem actualEsseCausePriorityViaDependence {W B R : Type} (m : Profile W B) (w : W)
    (CausesIn : B → B → R → Prop) (esse : R) (D PriorSimply : B → B → Prop)
    (hScoped : ActualDistinctDependencePriority m w D PriorSimply)
    (hDep : EsseEffectDependsOnItsCause CausesIn esse D)
    (hExists : EsseCausesExistAt m w CausesIn esse)
    (hConcrete : EsseCausesAreConcrete m CausesIn esse) :
    ActualEsseCausePriority m w CausesIn esse PriorSimply := by
  intro c x hne hx hc
  exact hScoped c x hne hx ⟨hConcrete c x hc, hExists c x hx hc⟩ (hDep c x hne hc)

/-- Theta.8 route with efficient-cause priority and the cause-to-efficient
bridge replaced by distinct-esse-cause priority: composes
`ActPriorityThetaEight.inActOfIncorruptible`'s step (a first being is in act in
being) with `EsseCausePriority.firstBeingNoPotencyOfEssePriority`. -/
theorem firstBeingNoPotencyOfThetaEightEsse {B R : Type}
    (InAct InPotency CanFailToBe : B → R → Prop) (PriorSimply : B → B → Prop)
    (Composite : B → Prop) (CausesIn : B → B → R → Prop) (esse : R)
    (hIncorruptible : FirstBeingIsIncorruptibleSimply CanFailToBe esse PriorSimply)
    (hInAct : IncorruptibleIsInActReading InAct CanFailToBe esse)
    (hComposite : ActInBeingAndPotencyMakeComposite InAct InPotency esse Composite)
    (hCause : CompositeHasAUnitingCauseReading Composite CausesIn esse)
    (hPrior : DistinctEsseCausePriority CausesIn esse PriorSimply) :
    FirstBeingIsInNoWayInPotencyReading InPotency PriorSimply :=
  TruthCore.Results.Causality.EsseCausePriority.firstBeingNoPotencyOfEssePriority
    (fun x _ => InAct x esse) InPotency PriorSimply Composite CausesIn esse
    (fun f hFirst => ⟨esse, hInAct f (hIncorruptible f hFirst)⟩)
    (fun x r _ hAct hPot => hComposite x r hAct hPot) hCause hPrior

/-- The first-being version of act priority from the same five premises: it
holds vacuously by `firstBeingNoPotencyOfThetaEightEsse`. -/
theorem weakOfThetaEightEsse {B R : Type}
    (InAct InPotency CanFailToBe : B → R → Prop) (PriorSimply : B → B → Prop)
    (Composite : B → Prop) (CausesIn : B → B → R → Prop) (esse : R)
    (hIncorruptible : FirstBeingIsIncorruptibleSimply CanFailToBe esse PriorSimply)
    (hInAct : IncorruptibleIsInActReading InAct CanFailToBe esse)
    (hComposite : ActInBeingAndPotencyMakeComposite InAct InPotency esse Composite)
    (hCause : CompositeHasAUnitingCauseReading Composite CausesIn esse)
    (hPrior : DistinctEsseCausePriority CausesIn esse PriorSimply) :
    FirstBeingActPriority InAct InPotency PriorSimply := by
  intro f hFirst r hPot
  exact absurd hPot (firstBeingNoPotencyOfThetaEightEsse InAct InPotency CanFailToBe
    PriorSimply Composite CausesIn esse hIncorruptible hInAct hComposite hCause hPrior f hFirst r)

/-! ## Distinct-relata siblings of the unrestricted bridge's consumers

Each existing consumer below applies `ActualDependenceIsGrounding` only to
distinct relata. The sibling takes the distinct-relata bridge instead, with the
other premises unchanged. -/

/-- Sibling of `Round2Grounding.esseCauseGroundViaDependence`. -/
theorem esseCauseGroundViaDistinctDependence {W B R : Type} (m : Profile W B) (w : W)
    (CausesIn : B → B → R → Prop) (esse : R) (D : B → B → Prop)
    (hExists : EsseCausesExistAt m w CausesIn esse)
    (hConcrete : EsseCausesAreConcrete m CausesIn esse)
    (hDep : EsseEffectDependsOnItsCause CausesIn esse D)
    (hGround : ActualDistinctDependenceIsGrounding m w D) :
    EsseCauseIsActualConcreteGround m w CausesIn esse := by
  intro c x hne hx hc
  have hcC : m.concrete c := hConcrete c x hc
  have hcE : m.ontic.ExistsAt w c := hExists c x hx hc
  exact ⟨hcC, hcE, hGround c x hne hx ⟨hcC, hcE⟩ (hDep c x hne hc)⟩

/-- Sibling of `CauseOfBeingHasBeing.esseCauseGroundOfExistentConcreteness`. -/
theorem esseCauseGroundOfExistentConcretenessViaDistinct {W B R : Type} (m : Profile W B)
    (w : W) (CausesIn : B → B → R → Prop) (esse : R) (D : B → B → Prop)
    (hExists : EsseCausesExistAt m w CausesIn esse)
    (hConcrete : EveryExistentConcreteAt m.ontic m.concrete w)
    (hDep : EsseEffectDependsOnItsCause CausesIn esse D)
    (hGround : ActualDistinctDependenceIsGrounding m w D) :
    EsseCauseIsActualConcreteGround m w CausesIn esse := by
  intro c x hne hx hc
  have hcE : m.ontic.ExistsAt w c := hExists c x hx hc
  have hcC : m.concrete c := hConcrete c hcE
  exact ⟨hcC, hcE, hGround c x hne hx ⟨hcC, hcE⟩ (hDep c x hne hc)⟩

/-- Sibling of `Round2Grounding.simplyPriorGroundViaDependence`. -/
theorem simplyPriorGroundViaDistinctDependence {W B : Type} (m : Profile W B) (w : W)
    (PriorSimply D : B → B → Prop)
    (hReq : PriorityRequiresNonmutualDependence PriorSimply D)
    (hRel : SimplePriorityRelatesActualConcreta m w PriorSimply)
    (hGround : ActualDistinctDependenceIsGrounding m w D) :
    SimplyPriorIsActualConcreteGround m w PriorSimply := by
  intro y x hne hp
  obtain ⟨hy, hx⟩ := hRel y x hp
  exact ⟨hy.1, hy.2, hGround y x hne hx hy (hReq y x hp).1⟩

/-! ## Why the distinct-relata version matters -/

/-- Reflexive dependence, the unrestricted dependence-to-grounding bridge,
actual grounding as simple priority and priority requiring nonmutual dependence
exclude every actual concretum: each would ground itself, hence be prior to
itself, hence both depend and not depend on itself. -/
theorem reflexiveUnrestrictedExcludesActualConcreta {W B : Type} (m : Profile W B) (w : W)
    (D PriorSimply : B → B → Prop)
    (hRefl : DependenceForBeingReflexive D)
    (hGround : ActualDependenceIsGrounding m w D)
    (hPrior : ActualGroundingIsSimplePriority m w PriorSimply)
    (hReq : PriorityRequiresNonmutualDependence PriorSimply D) :
    NoActualConcretumAt m w := by
  intro a ha
  have hSelf : PriorSimply a a := hPrior a a ha ha (hGround a a ha ha (hRefl a))
  exact (hReq a a hSelf).2 (hReq a a hSelf).1

/-! ## Controls -/

/-- The batch controls. -/
theorem controls : TruthCore.Causality.DependenceGroundingPriority.Control.Certificate := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- ReflexiveCompatible
    refine ⟨fun _ => Or.inl rfl, ?_, ?_, ?_, ⟨trivial, trivial⟩, ⟨trivial, trivial⟩,
      Or.inr ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩
    · intro c x hne _ _ hD
      rcases hD with h | ⟨hx, hc⟩
      · exact absurd h.symm hne
      · exact ⟨rfl, hc, hx⟩
    · intro a b _ _ h
      exact ⟨h.2.1, h.2.2⟩
    · rintro y x ⟨rfl, rfl⟩
      refine ⟨Or.inr ⟨rfl, rfl⟩, ?_⟩
      rintro (h | ⟨h, _⟩) <;> exact Bool.noConfusion h
  · -- UnrestrictedFails
    intro h
    obtain ⟨_, _, h1⟩ := h true true ⟨trivial, trivial⟩ ⟨trivial, trivial⟩ (Or.inl rfl)
    exact Bool.noConfusion h1
  · -- OmitDistinctGround
    refine ⟨fun _ _ _ _ h => h.elim, fun h => ?_⟩
    exact h true false Bool.noConfusion ⟨trivial, trivial⟩ ⟨trivial, trivial⟩ (Or.inr ⟨rfl, rfl⟩)
  · -- OmitGroundingPriority
    refine ⟨?_, fun h => ?_⟩
    · intro c x hne _ _ hD
      rcases hD with h | ⟨hx, hc⟩
      · exact absurd h.symm hne
      · exact ⟨rfl, hc, hx⟩
    · exact h true false Bool.noConfusion ⟨trivial, trivial⟩ ⟨trivial, trivial⟩ (Or.inr ⟨rfl, rfl⟩)

end TruthCore.Results.Causality.DependenceGroundingPriority
