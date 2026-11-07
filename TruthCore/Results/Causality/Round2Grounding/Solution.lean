module

public import TruthCore.Causality.Round2Grounding

@[expose] public section

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
  intro c x hne hx hc
  have hcC : m.concrete c := hConcrete c x hc
  have hcE : m.ontic.ExistsAt w c := hExists c x hx hc
  exact ⟨hcC, hcE, hGround c x hx ⟨hcC, hcE⟩ (hDep c x hne hc)⟩

/-- Map 3 (simply prior), dependence route. The simply prior is depended on by
what is posterior to it; both are actual concreta; dependence between actual
concreta is grounding. -/
theorem simplyPriorGroundViaDependence {W B : Type} (m : Profile W B) (w : W)
    (PriorSimply DependsForBeing : B → B → Prop)
    (hReq : PriorityRequiresNonmutualDependence PriorSimply DependsForBeing)
    (hRel : SimplePriorityRelatesActualConcreta m w PriorSimply)
    (hGround : ActualDependenceIsGrounding m w DependsForBeing) :
    SimplyPriorIsActualConcreteGround m w PriorSimply := by
  intro y x _ hp
  obtain ⟨hy, hx⟩ := hRel y x hp
  exact ⟨hy.1, hy.2, hGround y x hx hy (hReq y x hp).1⟩

/-- Map 3 (simply prior), esse-cause route: composes the stage-one premise that
the simply prior causes the esse of what is posterior with the esse-cause bridge. -/
theorem simplyPriorGroundViaEsseCause {W B R : Type} (m : Profile W B) (w : W)
    (PriorSimply : B → B → Prop) (CausesIn : B → B → R → Prop) (esse : R)
    (hCause : SimplyPriorIsCauseOfBeing PriorSimply CausesIn esse)
    (hRel : SimplePriorityRelatesActualConcreta m w PriorSimply)
    (hEsse : EsseCauseIsActualConcreteGround m w CausesIn esse) :
    SimplyPriorIsActualConcreteGround m w PriorSimply := by
  intro y x hne hp
  have hx : ActualConcrete m w x := (hRel y x hp).2
  have hc : CausesIn y x esse := hCause y x hp
  exact hEsse y x hne hx hc

/-- Map 4 (necessity causes), esse-cause route. -/
theorem necessityCauseGroundViaEsseCause {W B R : Type} (m : Profile W B) (w : W)
    (CausesNecessityOf : B → B → Prop) (CausesIn : B → B → R → Prop) (esse : R)
    (hCause : NecessityCauseCausesEsse CausesNecessityOf CausesIn esse)
    (hRel : NecessityCauseRelataActualConcrete m w CausesNecessityOf)
    (hEsse : EsseCauseIsActualConcreteGround m w CausesIn esse) :
    NecessityCausesAreActualConcreteGrounds m w CausesNecessityOf := by
  intro c x hne hc
  have hx : ActualConcrete m w x := (hRel c x hc).2
  have hEsseCause : CausesIn c x esse := hCause c x hc
  exact hEsse c x hne hx hEsseCause

/-- Map 4 (necessity causes), dependence route. -/
theorem necessityCauseGroundViaDependence {W B : Type} (m : Profile W B) (w : W)
    (CausesNecessityOf DependsForBeing : B → B → Prop)
    (hDep : NecessitatedDependsOnItsCause CausesNecessityOf DependsForBeing)
    (hRel : NecessityCauseRelataActualConcrete m w CausesNecessityOf)
    (hGround : ActualDependenceIsGrounding m w DependsForBeing) :
    NecessityCausesAreActualConcreteGrounds m w CausesNecessityOf := by
  intro c x _ hc
  obtain ⟨hcA, hxA⟩ := hRel c x hc
  exact ⟨hcA.1, hcA.2, hGround c x hxA hcA (hDep c x hc)⟩

/-- Map 1 (contingent grounded), participation route: an actual contingent
concretum has participated esse, so a distinct cause of its esse, which by the
esse-cause bridge is an actual concrete ground. -/
theorem contingentGroundedViaParticipation {W B R : Type} (m : Profile W B) (w : W)
    (Participates : B → Prop) (CausesIn : B → B → R → Prop) (esse : R)
    (hPart : ContingentConcretumParticipatesEsse m w Participates)
    (hCause : ParticipatedEsseHasDistinctCause Participates CausesIn esse)
    (hEsse : EsseCauseIsActualConcreteGround m w CausesIn esse) :
    EveryContingentGroundedAt m w := by
  intro x hxC hxE hcont
  obtain ⟨c, hne, hc⟩ := hCause x (hPart x ⟨hxC, hxE⟩ hcont)
  exact ⟨c, hEsse c x hne ⟨hxC, hxE⟩ hc⟩

/-- Map 1, Kantian local-cause route: the local causal principle supplies an
existing distinct cause, which the bridge makes a concrete ground. -/
theorem contingentGroundedViaLocalCause {W B : Type} (m : Profile W B) (w : W)
    (hLocal : LocalCausalPrinciple m.ontic)
    (hBridge : ExistingCauseOfActualConcretumIsConcreteGround m w) :
    EveryContingentGroundedAt m w := by
  intro x hxC hxE hcont
  obtain ⟨y, hyE, hyx, _⟩ := hLocal w x hcont
  obtain ⟨hyC, hg⟩ := hBridge y x ⟨hxC, hxE⟩ hyE hyx
  exact ⟨y, hyC, hyE, hg⟩

/-- Map 1, dependence route. -/
theorem contingentGroundedViaDependence {W B : Type} (m : Profile W B) (w : W)
    (DependsForBeing : B → B → Prop)
    (hDep : ActualContingentDependsOnActualConcretum m w DependsForBeing)
    (hGround : ActualDependenceIsGrounding m w DependsForBeing) :
    EveryContingentGroundedAt m w := by
  intro x hxC hxE hcont
  obtain ⟨y, hy, hxy⟩ := hDep x ⟨hxC, hxE⟩ hcont
  exact ⟨y, hy.1, hy.2, hGround y x ⟨hxC, hxE⟩ hy hxy⟩

/-- Map 5 (asymmetry): restricted well-foundedness gives asymmetry. Reuses
`actualGroundingAsymmetricOfWF`. -/
theorem asymmetricFromWF {W B : Type} (m : Profile W B) (w : W)
    (hWF : ActualGroundingWF m w) : ActualGroundingAsymmetric m w := by
  intro a b ha hb hab hba
  have hAsym : ActualGroundingAsymmetric m w := actualGroundingAsymmetricOfWF m w hWF
  exact hAsym a b ha hb hab hba

/-- Map 5, priority route: a reciprocal pair would make each simply prior to the
other, so each would depend and not depend on the other. -/
theorem asymmetricViaPriority {W B : Type} (m : Profile W B) (w : W)
    (PriorSimply DependsForBeing : B → B → Prop)
    (hPrior : ActualGroundingIsSimplePriority m w PriorSimply)
    (hReq : PriorityRequiresNonmutualDependence PriorSimply DependsForBeing) :
    ActualGroundingAsymmetric m w := by
  intro a b ha hb hab hba
  have h1 := hReq a b (hPrior a b ha hb hab)
  have h2 := hReq b a (hPrior b a hb ha hba)
  exact h1.2 h2.1

/-- Map 5, dependence route. -/
theorem asymmetricViaDependence {W B : Type} (m : Profile W B) (w : W)
    (DependsForBeing : B → B → Prop)
    (hDep : ActualGroundingIsDependence m w DependsForBeing)
    (hAsym : DependenceForBeingAsymmetric DependsForBeing) :
    ActualGroundingAsymmetric m w := by
  intro a b ha hb hab hba
  have hba' : DependsForBeing b a := hDep a b ha hb hab
  have hab' : DependsForBeing a b := hDep b a hb ha hba
  exact hAsym b a hba' hab'

/-- Map 5, grades route: a ground is more in esse than what it grounds, and
"more in" is asymmetric. -/
theorem asymmetricViaGrades {W B R : Type} (m : Profile W B) (w : W)
    (MoreIn : R → B → B → Prop) (esse : R)
    (hMore : ActualGroundIsMoreInEsse m w MoreIn esse)
    (hAsym : MoreInIsAsymmetric MoreIn) :
    ActualGroundingAsymmetric m w := by
  intro a b ha hb hab hba
  have h1 : MoreIn esse a b := hMore a b ha hb hab
  have h2 : MoreIn esse b a := hMore b a hb ha hba
  exact hAsym esse a b h1 h2

/-- Map 6 (maximal target), grades route: nothing actual grounds a maximum in
esse at all, since its ground would be more in esse than it. The `InAct` part of
maximality is unused. -/
theorem atMaximalTargetViaGrades {W B R : Type} (m : Profile W B) (w : W)
    (InAct : B → R → Prop) (MoreIn : R → B → B → Prop) (esse : R)
    (hMore : ActualGroundIsMoreInEsse m w MoreIn esse) :
    AtMaximalTarget m w InAct MoreIn esse := by
  intro a b ha hb hMax hab _
  have hGreater : MoreIn esse a b := hMore a b ha hb hab
  have hNone : ∀ y, ¬ MoreIn esse y b := hMax.2
  exact hNone a hGreater

/-! ## Controls -/

open TruthCore.Causality.CogitoNecessaryConcrete (ActualConcreteGround)
open TruthCore.German.Kant.CosmologicalInference (ContingentAt)

theorem esseCauseGroundViaDependence_omit_hGround : Control.esseCauseGroundViaDependence.omit_hGround.Holds := by
  open Control.esseCauseGroundViaDependence.omit_hGround in
  dsimp only [Holds, EsseCausesExistAt, EsseCausesAreConcrete, EsseEffectDependsOnItsCause, ActualDependenceIsGrounding, SimplePriorityRelatesActualConcreta, NecessityCauseCausesEsse, NecessityCauseRelataActualConcrete, NecessitatedDependsOnItsCause, ContingentConcretumParticipatesEsse, ParticipatedEsseHasDistinctCause, ActualContingentDependsOnActualConcretum, ExistingCauseOfActualConcretumIsConcreteGround, ActualGroundingIsSimplePriority, ActualGroundingIsDependence, DependenceForBeingAsymmetric, ActualGroundIsMoreInEsse, ActualConcrete, ActualConcreteGround, EsseCauseIsActualConcreteGround, SimplyPriorIsActualConcreteGround, NecessityCausesAreActualConcreteGrounds, EveryContingentGroundedAt, ContingentAt, LocalCausalPrinciple, ActualGroundingAsymmetric, AtMaximalTarget, IsMaximumIn, PriorityRequiresNonmutualDependence, SimplyPriorIsCauseOfBeing, MoreInIsAsymmetric, m, Control.mk, acc, ex, conc, cau, gr, C, D, P, N, Partic, More, Act]
  and_intros <;> decide

theorem esseCauseGroundViaDependence_omit_hExists : Control.esseCauseGroundViaDependence.omit_hExists.Holds := by
  open Control.esseCauseGroundViaDependence.omit_hExists in
  dsimp only [Holds, EsseCausesExistAt, EsseCausesAreConcrete, EsseEffectDependsOnItsCause, ActualDependenceIsGrounding, SimplePriorityRelatesActualConcreta, NecessityCauseCausesEsse, NecessityCauseRelataActualConcrete, NecessitatedDependsOnItsCause, ContingentConcretumParticipatesEsse, ParticipatedEsseHasDistinctCause, ActualContingentDependsOnActualConcretum, ExistingCauseOfActualConcretumIsConcreteGround, ActualGroundingIsSimplePriority, ActualGroundingIsDependence, DependenceForBeingAsymmetric, ActualGroundIsMoreInEsse, ActualConcrete, ActualConcreteGround, EsseCauseIsActualConcreteGround, SimplyPriorIsActualConcreteGround, NecessityCausesAreActualConcreteGrounds, EveryContingentGroundedAt, ContingentAt, LocalCausalPrinciple, ActualGroundingAsymmetric, AtMaximalTarget, IsMaximumIn, PriorityRequiresNonmutualDependence, SimplyPriorIsCauseOfBeing, MoreInIsAsymmetric, m, Control.mk, acc, ex, conc, cau, gr, C, D, P, N, Partic, More, Act]
  and_intros <;> decide

theorem esseCauseGroundViaDependence_omit_hConcrete : Control.esseCauseGroundViaDependence.omit_hConcrete.Holds := by
  open Control.esseCauseGroundViaDependence.omit_hConcrete in
  dsimp only [Holds, EsseCausesExistAt, EsseCausesAreConcrete, EsseEffectDependsOnItsCause, ActualDependenceIsGrounding, SimplePriorityRelatesActualConcreta, NecessityCauseCausesEsse, NecessityCauseRelataActualConcrete, NecessitatedDependsOnItsCause, ContingentConcretumParticipatesEsse, ParticipatedEsseHasDistinctCause, ActualContingentDependsOnActualConcretum, ExistingCauseOfActualConcretumIsConcreteGround, ActualGroundingIsSimplePriority, ActualGroundingIsDependence, DependenceForBeingAsymmetric, ActualGroundIsMoreInEsse, ActualConcrete, ActualConcreteGround, EsseCauseIsActualConcreteGround, SimplyPriorIsActualConcreteGround, NecessityCausesAreActualConcreteGrounds, EveryContingentGroundedAt, ContingentAt, LocalCausalPrinciple, ActualGroundingAsymmetric, AtMaximalTarget, IsMaximumIn, PriorityRequiresNonmutualDependence, SimplyPriorIsCauseOfBeing, MoreInIsAsymmetric, m, Control.mk, acc, ex, conc, cau, gr, C, D, P, N, Partic, More, Act]
  and_intros <;> decide

theorem esseCauseGroundViaDependence_omit_hDep : Control.esseCauseGroundViaDependence.omit_hDep.Holds := by
  open Control.esseCauseGroundViaDependence.omit_hDep in
  dsimp only [Holds, EsseCausesExistAt, EsseCausesAreConcrete, EsseEffectDependsOnItsCause, ActualDependenceIsGrounding, SimplePriorityRelatesActualConcreta, NecessityCauseCausesEsse, NecessityCauseRelataActualConcrete, NecessitatedDependsOnItsCause, ContingentConcretumParticipatesEsse, ParticipatedEsseHasDistinctCause, ActualContingentDependsOnActualConcretum, ExistingCauseOfActualConcretumIsConcreteGround, ActualGroundingIsSimplePriority, ActualGroundingIsDependence, DependenceForBeingAsymmetric, ActualGroundIsMoreInEsse, ActualConcrete, ActualConcreteGround, EsseCauseIsActualConcreteGround, SimplyPriorIsActualConcreteGround, NecessityCausesAreActualConcreteGrounds, EveryContingentGroundedAt, ContingentAt, LocalCausalPrinciple, ActualGroundingAsymmetric, AtMaximalTarget, IsMaximumIn, PriorityRequiresNonmutualDependence, SimplyPriorIsCauseOfBeing, MoreInIsAsymmetric, m, Control.mk, acc, ex, conc, cau, gr, C, D, P, N, Partic, More, Act]
  and_intros <;> decide

theorem simplyPriorGroundViaDependence_omit_hReq : Control.simplyPriorGroundViaDependence.omit_hReq.Holds := by
  open Control.simplyPriorGroundViaDependence.omit_hReq in
  dsimp only [Holds, EsseCausesExistAt, EsseCausesAreConcrete, EsseEffectDependsOnItsCause, ActualDependenceIsGrounding, SimplePriorityRelatesActualConcreta, NecessityCauseCausesEsse, NecessityCauseRelataActualConcrete, NecessitatedDependsOnItsCause, ContingentConcretumParticipatesEsse, ParticipatedEsseHasDistinctCause, ActualContingentDependsOnActualConcretum, ExistingCauseOfActualConcretumIsConcreteGround, ActualGroundingIsSimplePriority, ActualGroundingIsDependence, DependenceForBeingAsymmetric, ActualGroundIsMoreInEsse, ActualConcrete, ActualConcreteGround, EsseCauseIsActualConcreteGround, SimplyPriorIsActualConcreteGround, NecessityCausesAreActualConcreteGrounds, EveryContingentGroundedAt, ContingentAt, LocalCausalPrinciple, ActualGroundingAsymmetric, AtMaximalTarget, IsMaximumIn, PriorityRequiresNonmutualDependence, SimplyPriorIsCauseOfBeing, MoreInIsAsymmetric, m, Control.mk, acc, ex, conc, cau, gr, C, D, P, N, Partic, More, Act]
  and_intros <;> decide

theorem simplyPriorGroundViaDependence_omit_hRel : Control.simplyPriorGroundViaDependence.omit_hRel.Holds := by
  open Control.simplyPriorGroundViaDependence.omit_hRel in
  dsimp only [Holds, EsseCausesExistAt, EsseCausesAreConcrete, EsseEffectDependsOnItsCause, ActualDependenceIsGrounding, SimplePriorityRelatesActualConcreta, NecessityCauseCausesEsse, NecessityCauseRelataActualConcrete, NecessitatedDependsOnItsCause, ContingentConcretumParticipatesEsse, ParticipatedEsseHasDistinctCause, ActualContingentDependsOnActualConcretum, ExistingCauseOfActualConcretumIsConcreteGround, ActualGroundingIsSimplePriority, ActualGroundingIsDependence, DependenceForBeingAsymmetric, ActualGroundIsMoreInEsse, ActualConcrete, ActualConcreteGround, EsseCauseIsActualConcreteGround, SimplyPriorIsActualConcreteGround, NecessityCausesAreActualConcreteGrounds, EveryContingentGroundedAt, ContingentAt, LocalCausalPrinciple, ActualGroundingAsymmetric, AtMaximalTarget, IsMaximumIn, PriorityRequiresNonmutualDependence, SimplyPriorIsCauseOfBeing, MoreInIsAsymmetric, m, Control.mk, acc, ex, conc, cau, gr, C, D, P, N, Partic, More, Act]
  and_intros <;> decide

theorem simplyPriorGroundViaDependence_omit_hGround : Control.simplyPriorGroundViaDependence.omit_hGround.Holds := by
  open Control.simplyPriorGroundViaDependence.omit_hGround in
  dsimp only [Holds, EsseCausesExistAt, EsseCausesAreConcrete, EsseEffectDependsOnItsCause, ActualDependenceIsGrounding, SimplePriorityRelatesActualConcreta, NecessityCauseCausesEsse, NecessityCauseRelataActualConcrete, NecessitatedDependsOnItsCause, ContingentConcretumParticipatesEsse, ParticipatedEsseHasDistinctCause, ActualContingentDependsOnActualConcretum, ExistingCauseOfActualConcretumIsConcreteGround, ActualGroundingIsSimplePriority, ActualGroundingIsDependence, DependenceForBeingAsymmetric, ActualGroundIsMoreInEsse, ActualConcrete, ActualConcreteGround, EsseCauseIsActualConcreteGround, SimplyPriorIsActualConcreteGround, NecessityCausesAreActualConcreteGrounds, EveryContingentGroundedAt, ContingentAt, LocalCausalPrinciple, ActualGroundingAsymmetric, AtMaximalTarget, IsMaximumIn, PriorityRequiresNonmutualDependence, SimplyPriorIsCauseOfBeing, MoreInIsAsymmetric, m, Control.mk, acc, ex, conc, cau, gr, C, D, P, N, Partic, More, Act]
  and_intros <;> decide

theorem simplyPriorGroundViaEsseCause_omit_hCause : Control.simplyPriorGroundViaEsseCause.omit_hCause.Holds := by
  open Control.simplyPriorGroundViaEsseCause.omit_hCause in
  dsimp only [Holds, EsseCausesExistAt, EsseCausesAreConcrete, EsseEffectDependsOnItsCause, ActualDependenceIsGrounding, SimplePriorityRelatesActualConcreta, NecessityCauseCausesEsse, NecessityCauseRelataActualConcrete, NecessitatedDependsOnItsCause, ContingentConcretumParticipatesEsse, ParticipatedEsseHasDistinctCause, ActualContingentDependsOnActualConcretum, ExistingCauseOfActualConcretumIsConcreteGround, ActualGroundingIsSimplePriority, ActualGroundingIsDependence, DependenceForBeingAsymmetric, ActualGroundIsMoreInEsse, ActualConcrete, ActualConcreteGround, EsseCauseIsActualConcreteGround, SimplyPriorIsActualConcreteGround, NecessityCausesAreActualConcreteGrounds, EveryContingentGroundedAt, ContingentAt, LocalCausalPrinciple, ActualGroundingAsymmetric, AtMaximalTarget, IsMaximumIn, PriorityRequiresNonmutualDependence, SimplyPriorIsCauseOfBeing, MoreInIsAsymmetric, m, Control.mk, acc, ex, conc, cau, gr, C, D, P, N, Partic, More, Act]
  and_intros <;> decide

theorem simplyPriorGroundViaEsseCause_omit_hRel : Control.simplyPriorGroundViaEsseCause.omit_hRel.Holds := by
  open Control.simplyPriorGroundViaEsseCause.omit_hRel in
  dsimp only [Holds, EsseCausesExistAt, EsseCausesAreConcrete, EsseEffectDependsOnItsCause, ActualDependenceIsGrounding, SimplePriorityRelatesActualConcreta, NecessityCauseCausesEsse, NecessityCauseRelataActualConcrete, NecessitatedDependsOnItsCause, ContingentConcretumParticipatesEsse, ParticipatedEsseHasDistinctCause, ActualContingentDependsOnActualConcretum, ExistingCauseOfActualConcretumIsConcreteGround, ActualGroundingIsSimplePriority, ActualGroundingIsDependence, DependenceForBeingAsymmetric, ActualGroundIsMoreInEsse, ActualConcrete, ActualConcreteGround, EsseCauseIsActualConcreteGround, SimplyPriorIsActualConcreteGround, NecessityCausesAreActualConcreteGrounds, EveryContingentGroundedAt, ContingentAt, LocalCausalPrinciple, ActualGroundingAsymmetric, AtMaximalTarget, IsMaximumIn, PriorityRequiresNonmutualDependence, SimplyPriorIsCauseOfBeing, MoreInIsAsymmetric, m, Control.mk, acc, ex, conc, cau, gr, C, D, P, N, Partic, More, Act]
  and_intros <;> decide

theorem simplyPriorGroundViaEsseCause_omit_hEsse : Control.simplyPriorGroundViaEsseCause.omit_hEsse.Holds := by
  open Control.simplyPriorGroundViaEsseCause.omit_hEsse in
  dsimp only [Holds, EsseCausesExistAt, EsseCausesAreConcrete, EsseEffectDependsOnItsCause, ActualDependenceIsGrounding, SimplePriorityRelatesActualConcreta, NecessityCauseCausesEsse, NecessityCauseRelataActualConcrete, NecessitatedDependsOnItsCause, ContingentConcretumParticipatesEsse, ParticipatedEsseHasDistinctCause, ActualContingentDependsOnActualConcretum, ExistingCauseOfActualConcretumIsConcreteGround, ActualGroundingIsSimplePriority, ActualGroundingIsDependence, DependenceForBeingAsymmetric, ActualGroundIsMoreInEsse, ActualConcrete, ActualConcreteGround, EsseCauseIsActualConcreteGround, SimplyPriorIsActualConcreteGround, NecessityCausesAreActualConcreteGrounds, EveryContingentGroundedAt, ContingentAt, LocalCausalPrinciple, ActualGroundingAsymmetric, AtMaximalTarget, IsMaximumIn, PriorityRequiresNonmutualDependence, SimplyPriorIsCauseOfBeing, MoreInIsAsymmetric, m, Control.mk, acc, ex, conc, cau, gr, C, D, P, N, Partic, More, Act]
  and_intros <;> decide

theorem necessityCauseGroundViaEsseCause_omit_hCause : Control.necessityCauseGroundViaEsseCause.omit_hCause.Holds := by
  open Control.necessityCauseGroundViaEsseCause.omit_hCause in
  dsimp only [Holds, EsseCausesExistAt, EsseCausesAreConcrete, EsseEffectDependsOnItsCause, ActualDependenceIsGrounding, SimplePriorityRelatesActualConcreta, NecessityCauseCausesEsse, NecessityCauseRelataActualConcrete, NecessitatedDependsOnItsCause, ContingentConcretumParticipatesEsse, ParticipatedEsseHasDistinctCause, ActualContingentDependsOnActualConcretum, ExistingCauseOfActualConcretumIsConcreteGround, ActualGroundingIsSimplePriority, ActualGroundingIsDependence, DependenceForBeingAsymmetric, ActualGroundIsMoreInEsse, ActualConcrete, ActualConcreteGround, EsseCauseIsActualConcreteGround, SimplyPriorIsActualConcreteGround, NecessityCausesAreActualConcreteGrounds, EveryContingentGroundedAt, ContingentAt, LocalCausalPrinciple, ActualGroundingAsymmetric, AtMaximalTarget, IsMaximumIn, PriorityRequiresNonmutualDependence, SimplyPriorIsCauseOfBeing, MoreInIsAsymmetric, m, Control.mk, acc, ex, conc, cau, gr, C, D, P, N, Partic, More, Act]
  and_intros <;> decide

theorem necessityCauseGroundViaEsseCause_omit_hRel : Control.necessityCauseGroundViaEsseCause.omit_hRel.Holds := by
  open Control.necessityCauseGroundViaEsseCause.omit_hRel in
  dsimp only [Holds, EsseCausesExistAt, EsseCausesAreConcrete, EsseEffectDependsOnItsCause, ActualDependenceIsGrounding, SimplePriorityRelatesActualConcreta, NecessityCauseCausesEsse, NecessityCauseRelataActualConcrete, NecessitatedDependsOnItsCause, ContingentConcretumParticipatesEsse, ParticipatedEsseHasDistinctCause, ActualContingentDependsOnActualConcretum, ExistingCauseOfActualConcretumIsConcreteGround, ActualGroundingIsSimplePriority, ActualGroundingIsDependence, DependenceForBeingAsymmetric, ActualGroundIsMoreInEsse, ActualConcrete, ActualConcreteGround, EsseCauseIsActualConcreteGround, SimplyPriorIsActualConcreteGround, NecessityCausesAreActualConcreteGrounds, EveryContingentGroundedAt, ContingentAt, LocalCausalPrinciple, ActualGroundingAsymmetric, AtMaximalTarget, IsMaximumIn, PriorityRequiresNonmutualDependence, SimplyPriorIsCauseOfBeing, MoreInIsAsymmetric, m, Control.mk, acc, ex, conc, cau, gr, C, D, P, N, Partic, More, Act]
  and_intros <;> decide

theorem necessityCauseGroundViaEsseCause_omit_hEsse : Control.necessityCauseGroundViaEsseCause.omit_hEsse.Holds := by
  open Control.necessityCauseGroundViaEsseCause.omit_hEsse in
  dsimp only [Holds, EsseCausesExistAt, EsseCausesAreConcrete, EsseEffectDependsOnItsCause, ActualDependenceIsGrounding, SimplePriorityRelatesActualConcreta, NecessityCauseCausesEsse, NecessityCauseRelataActualConcrete, NecessitatedDependsOnItsCause, ContingentConcretumParticipatesEsse, ParticipatedEsseHasDistinctCause, ActualContingentDependsOnActualConcretum, ExistingCauseOfActualConcretumIsConcreteGround, ActualGroundingIsSimplePriority, ActualGroundingIsDependence, DependenceForBeingAsymmetric, ActualGroundIsMoreInEsse, ActualConcrete, ActualConcreteGround, EsseCauseIsActualConcreteGround, SimplyPriorIsActualConcreteGround, NecessityCausesAreActualConcreteGrounds, EveryContingentGroundedAt, ContingentAt, LocalCausalPrinciple, ActualGroundingAsymmetric, AtMaximalTarget, IsMaximumIn, PriorityRequiresNonmutualDependence, SimplyPriorIsCauseOfBeing, MoreInIsAsymmetric, m, Control.mk, acc, ex, conc, cau, gr, C, D, P, N, Partic, More, Act]
  and_intros <;> decide

theorem necessityCauseGroundViaDependence_omit_hDep : Control.necessityCauseGroundViaDependence.omit_hDep.Holds := by
  open Control.necessityCauseGroundViaDependence.omit_hDep in
  dsimp only [Holds, EsseCausesExistAt, EsseCausesAreConcrete, EsseEffectDependsOnItsCause, ActualDependenceIsGrounding, SimplePriorityRelatesActualConcreta, NecessityCauseCausesEsse, NecessityCauseRelataActualConcrete, NecessitatedDependsOnItsCause, ContingentConcretumParticipatesEsse, ParticipatedEsseHasDistinctCause, ActualContingentDependsOnActualConcretum, ExistingCauseOfActualConcretumIsConcreteGround, ActualGroundingIsSimplePriority, ActualGroundingIsDependence, DependenceForBeingAsymmetric, ActualGroundIsMoreInEsse, ActualConcrete, ActualConcreteGround, EsseCauseIsActualConcreteGround, SimplyPriorIsActualConcreteGround, NecessityCausesAreActualConcreteGrounds, EveryContingentGroundedAt, ContingentAt, LocalCausalPrinciple, ActualGroundingAsymmetric, AtMaximalTarget, IsMaximumIn, PriorityRequiresNonmutualDependence, SimplyPriorIsCauseOfBeing, MoreInIsAsymmetric, m, Control.mk, acc, ex, conc, cau, gr, C, D, P, N, Partic, More, Act]
  and_intros <;> decide

theorem necessityCauseGroundViaDependence_omit_hRel : Control.necessityCauseGroundViaDependence.omit_hRel.Holds := by
  open Control.necessityCauseGroundViaDependence.omit_hRel in
  dsimp only [Holds, EsseCausesExistAt, EsseCausesAreConcrete, EsseEffectDependsOnItsCause, ActualDependenceIsGrounding, SimplePriorityRelatesActualConcreta, NecessityCauseCausesEsse, NecessityCauseRelataActualConcrete, NecessitatedDependsOnItsCause, ContingentConcretumParticipatesEsse, ParticipatedEsseHasDistinctCause, ActualContingentDependsOnActualConcretum, ExistingCauseOfActualConcretumIsConcreteGround, ActualGroundingIsSimplePriority, ActualGroundingIsDependence, DependenceForBeingAsymmetric, ActualGroundIsMoreInEsse, ActualConcrete, ActualConcreteGround, EsseCauseIsActualConcreteGround, SimplyPriorIsActualConcreteGround, NecessityCausesAreActualConcreteGrounds, EveryContingentGroundedAt, ContingentAt, LocalCausalPrinciple, ActualGroundingAsymmetric, AtMaximalTarget, IsMaximumIn, PriorityRequiresNonmutualDependence, SimplyPriorIsCauseOfBeing, MoreInIsAsymmetric, m, Control.mk, acc, ex, conc, cau, gr, C, D, P, N, Partic, More, Act]
  and_intros <;> decide

theorem necessityCauseGroundViaDependence_omit_hGround : Control.necessityCauseGroundViaDependence.omit_hGround.Holds := by
  open Control.necessityCauseGroundViaDependence.omit_hGround in
  dsimp only [Holds, EsseCausesExistAt, EsseCausesAreConcrete, EsseEffectDependsOnItsCause, ActualDependenceIsGrounding, SimplePriorityRelatesActualConcreta, NecessityCauseCausesEsse, NecessityCauseRelataActualConcrete, NecessitatedDependsOnItsCause, ContingentConcretumParticipatesEsse, ParticipatedEsseHasDistinctCause, ActualContingentDependsOnActualConcretum, ExistingCauseOfActualConcretumIsConcreteGround, ActualGroundingIsSimplePriority, ActualGroundingIsDependence, DependenceForBeingAsymmetric, ActualGroundIsMoreInEsse, ActualConcrete, ActualConcreteGround, EsseCauseIsActualConcreteGround, SimplyPriorIsActualConcreteGround, NecessityCausesAreActualConcreteGrounds, EveryContingentGroundedAt, ContingentAt, LocalCausalPrinciple, ActualGroundingAsymmetric, AtMaximalTarget, IsMaximumIn, PriorityRequiresNonmutualDependence, SimplyPriorIsCauseOfBeing, MoreInIsAsymmetric, m, Control.mk, acc, ex, conc, cau, gr, C, D, P, N, Partic, More, Act]
  and_intros <;> decide

theorem contingentGroundedViaParticipation_omit_hPart : Control.contingentGroundedViaParticipation.omit_hPart.Holds := by
  open Control.contingentGroundedViaParticipation.omit_hPart in
  dsimp only [Holds, EsseCausesExistAt, EsseCausesAreConcrete, EsseEffectDependsOnItsCause, ActualDependenceIsGrounding, SimplePriorityRelatesActualConcreta, NecessityCauseCausesEsse, NecessityCauseRelataActualConcrete, NecessitatedDependsOnItsCause, ContingentConcretumParticipatesEsse, ParticipatedEsseHasDistinctCause, ActualContingentDependsOnActualConcretum, ExistingCauseOfActualConcretumIsConcreteGround, ActualGroundingIsSimplePriority, ActualGroundingIsDependence, DependenceForBeingAsymmetric, ActualGroundIsMoreInEsse, ActualConcrete, ActualConcreteGround, EsseCauseIsActualConcreteGround, SimplyPriorIsActualConcreteGround, NecessityCausesAreActualConcreteGrounds, EveryContingentGroundedAt, ContingentAt, LocalCausalPrinciple, ActualGroundingAsymmetric, AtMaximalTarget, IsMaximumIn, PriorityRequiresNonmutualDependence, SimplyPriorIsCauseOfBeing, MoreInIsAsymmetric, m, Control.mk, acc, ex, conc, cau, gr, C, D, P, N, Partic, More, Act]
  and_intros <;> decide

theorem contingentGroundedViaParticipation_omit_hCause : Control.contingentGroundedViaParticipation.omit_hCause.Holds := by
  open Control.contingentGroundedViaParticipation.omit_hCause in
  dsimp only [Holds, EsseCausesExistAt, EsseCausesAreConcrete, EsseEffectDependsOnItsCause, ActualDependenceIsGrounding, SimplePriorityRelatesActualConcreta, NecessityCauseCausesEsse, NecessityCauseRelataActualConcrete, NecessitatedDependsOnItsCause, ContingentConcretumParticipatesEsse, ParticipatedEsseHasDistinctCause, ActualContingentDependsOnActualConcretum, ExistingCauseOfActualConcretumIsConcreteGround, ActualGroundingIsSimplePriority, ActualGroundingIsDependence, DependenceForBeingAsymmetric, ActualGroundIsMoreInEsse, ActualConcrete, ActualConcreteGround, EsseCauseIsActualConcreteGround, SimplyPriorIsActualConcreteGround, NecessityCausesAreActualConcreteGrounds, EveryContingentGroundedAt, ContingentAt, LocalCausalPrinciple, ActualGroundingAsymmetric, AtMaximalTarget, IsMaximumIn, PriorityRequiresNonmutualDependence, SimplyPriorIsCauseOfBeing, MoreInIsAsymmetric, m, Control.mk, acc, ex, conc, cau, gr, C, D, P, N, Partic, More, Act]
  and_intros <;> decide

theorem contingentGroundedViaParticipation_omit_hEsse : Control.contingentGroundedViaParticipation.omit_hEsse.Holds := by
  open Control.contingentGroundedViaParticipation.omit_hEsse in
  dsimp only [Holds, EsseCausesExistAt, EsseCausesAreConcrete, EsseEffectDependsOnItsCause, ActualDependenceIsGrounding, SimplePriorityRelatesActualConcreta, NecessityCauseCausesEsse, NecessityCauseRelataActualConcrete, NecessitatedDependsOnItsCause, ContingentConcretumParticipatesEsse, ParticipatedEsseHasDistinctCause, ActualContingentDependsOnActualConcretum, ExistingCauseOfActualConcretumIsConcreteGround, ActualGroundingIsSimplePriority, ActualGroundingIsDependence, DependenceForBeingAsymmetric, ActualGroundIsMoreInEsse, ActualConcrete, ActualConcreteGround, EsseCauseIsActualConcreteGround, SimplyPriorIsActualConcreteGround, NecessityCausesAreActualConcreteGrounds, EveryContingentGroundedAt, ContingentAt, LocalCausalPrinciple, ActualGroundingAsymmetric, AtMaximalTarget, IsMaximumIn, PriorityRequiresNonmutualDependence, SimplyPriorIsCauseOfBeing, MoreInIsAsymmetric, m, Control.mk, acc, ex, conc, cau, gr, C, D, P, N, Partic, More, Act]
  and_intros <;> decide

theorem contingentGroundedViaLocalCause_omit_hLocal : Control.contingentGroundedViaLocalCause.omit_hLocal.Holds := by
  open Control.contingentGroundedViaLocalCause.omit_hLocal in
  dsimp only [Holds, EsseCausesExistAt, EsseCausesAreConcrete, EsseEffectDependsOnItsCause, ActualDependenceIsGrounding, SimplePriorityRelatesActualConcreta, NecessityCauseCausesEsse, NecessityCauseRelataActualConcrete, NecessitatedDependsOnItsCause, ContingentConcretumParticipatesEsse, ParticipatedEsseHasDistinctCause, ActualContingentDependsOnActualConcretum, ExistingCauseOfActualConcretumIsConcreteGround, ActualGroundingIsSimplePriority, ActualGroundingIsDependence, DependenceForBeingAsymmetric, ActualGroundIsMoreInEsse, ActualConcrete, ActualConcreteGround, EsseCauseIsActualConcreteGround, SimplyPriorIsActualConcreteGround, NecessityCausesAreActualConcreteGrounds, EveryContingentGroundedAt, ContingentAt, LocalCausalPrinciple, ActualGroundingAsymmetric, AtMaximalTarget, IsMaximumIn, PriorityRequiresNonmutualDependence, SimplyPriorIsCauseOfBeing, MoreInIsAsymmetric, m, Control.mk, acc, ex, conc, cau, gr, C, D, P, N, Partic, More, Act]
  and_intros <;> decide

theorem contingentGroundedViaLocalCause_omit_hBridge : Control.contingentGroundedViaLocalCause.omit_hBridge.Holds := by
  open Control.contingentGroundedViaLocalCause.omit_hBridge in
  dsimp only [Holds, EsseCausesExistAt, EsseCausesAreConcrete, EsseEffectDependsOnItsCause, ActualDependenceIsGrounding, SimplePriorityRelatesActualConcreta, NecessityCauseCausesEsse, NecessityCauseRelataActualConcrete, NecessitatedDependsOnItsCause, ContingentConcretumParticipatesEsse, ParticipatedEsseHasDistinctCause, ActualContingentDependsOnActualConcretum, ExistingCauseOfActualConcretumIsConcreteGround, ActualGroundingIsSimplePriority, ActualGroundingIsDependence, DependenceForBeingAsymmetric, ActualGroundIsMoreInEsse, ActualConcrete, ActualConcreteGround, EsseCauseIsActualConcreteGround, SimplyPriorIsActualConcreteGround, NecessityCausesAreActualConcreteGrounds, EveryContingentGroundedAt, ContingentAt, LocalCausalPrinciple, ActualGroundingAsymmetric, AtMaximalTarget, IsMaximumIn, PriorityRequiresNonmutualDependence, SimplyPriorIsCauseOfBeing, MoreInIsAsymmetric, m, Control.mk, acc, ex, conc, cau, gr, C, D, P, N, Partic, More, Act]
  and_intros <;> decide

theorem contingentGroundedViaDependence_omit_hDep : Control.contingentGroundedViaDependence.omit_hDep.Holds := by
  open Control.contingentGroundedViaDependence.omit_hDep in
  dsimp only [Holds, EsseCausesExistAt, EsseCausesAreConcrete, EsseEffectDependsOnItsCause, ActualDependenceIsGrounding, SimplePriorityRelatesActualConcreta, NecessityCauseCausesEsse, NecessityCauseRelataActualConcrete, NecessitatedDependsOnItsCause, ContingentConcretumParticipatesEsse, ParticipatedEsseHasDistinctCause, ActualContingentDependsOnActualConcretum, ExistingCauseOfActualConcretumIsConcreteGround, ActualGroundingIsSimplePriority, ActualGroundingIsDependence, DependenceForBeingAsymmetric, ActualGroundIsMoreInEsse, ActualConcrete, ActualConcreteGround, EsseCauseIsActualConcreteGround, SimplyPriorIsActualConcreteGround, NecessityCausesAreActualConcreteGrounds, EveryContingentGroundedAt, ContingentAt, LocalCausalPrinciple, ActualGroundingAsymmetric, AtMaximalTarget, IsMaximumIn, PriorityRequiresNonmutualDependence, SimplyPriorIsCauseOfBeing, MoreInIsAsymmetric, m, Control.mk, acc, ex, conc, cau, gr, C, D, P, N, Partic, More, Act]
  and_intros <;> decide

theorem contingentGroundedViaDependence_omit_hGround : Control.contingentGroundedViaDependence.omit_hGround.Holds := by
  open Control.contingentGroundedViaDependence.omit_hGround in
  dsimp only [Holds, EsseCausesExistAt, EsseCausesAreConcrete, EsseEffectDependsOnItsCause, ActualDependenceIsGrounding, SimplePriorityRelatesActualConcreta, NecessityCauseCausesEsse, NecessityCauseRelataActualConcrete, NecessitatedDependsOnItsCause, ContingentConcretumParticipatesEsse, ParticipatedEsseHasDistinctCause, ActualContingentDependsOnActualConcretum, ExistingCauseOfActualConcretumIsConcreteGround, ActualGroundingIsSimplePriority, ActualGroundingIsDependence, DependenceForBeingAsymmetric, ActualGroundIsMoreInEsse, ActualConcrete, ActualConcreteGround, EsseCauseIsActualConcreteGround, SimplyPriorIsActualConcreteGround, NecessityCausesAreActualConcreteGrounds, EveryContingentGroundedAt, ContingentAt, LocalCausalPrinciple, ActualGroundingAsymmetric, AtMaximalTarget, IsMaximumIn, PriorityRequiresNonmutualDependence, SimplyPriorIsCauseOfBeing, MoreInIsAsymmetric, m, Control.mk, acc, ex, conc, cau, gr, C, D, P, N, Partic, More, Act]
  and_intros <;> decide

theorem asymmetricViaPriority_omit_hPrior : Control.asymmetricViaPriority.omit_hPrior.Holds := by
  open Control.asymmetricViaPriority.omit_hPrior in
  dsimp only [Holds, EsseCausesExistAt, EsseCausesAreConcrete, EsseEffectDependsOnItsCause, ActualDependenceIsGrounding, SimplePriorityRelatesActualConcreta, NecessityCauseCausesEsse, NecessityCauseRelataActualConcrete, NecessitatedDependsOnItsCause, ContingentConcretumParticipatesEsse, ParticipatedEsseHasDistinctCause, ActualContingentDependsOnActualConcretum, ExistingCauseOfActualConcretumIsConcreteGround, ActualGroundingIsSimplePriority, ActualGroundingIsDependence, DependenceForBeingAsymmetric, ActualGroundIsMoreInEsse, ActualConcrete, ActualConcreteGround, EsseCauseIsActualConcreteGround, SimplyPriorIsActualConcreteGround, NecessityCausesAreActualConcreteGrounds, EveryContingentGroundedAt, ContingentAt, LocalCausalPrinciple, ActualGroundingAsymmetric, AtMaximalTarget, IsMaximumIn, PriorityRequiresNonmutualDependence, SimplyPriorIsCauseOfBeing, MoreInIsAsymmetric, m, Control.mk, acc, ex, conc, cau, gr, C, D, P, N, Partic, More, Act]
  and_intros <;> decide

theorem asymmetricViaPriority_omit_hReq : Control.asymmetricViaPriority.omit_hReq.Holds := by
  open Control.asymmetricViaPriority.omit_hReq in
  dsimp only [Holds, EsseCausesExistAt, EsseCausesAreConcrete, EsseEffectDependsOnItsCause, ActualDependenceIsGrounding, SimplePriorityRelatesActualConcreta, NecessityCauseCausesEsse, NecessityCauseRelataActualConcrete, NecessitatedDependsOnItsCause, ContingentConcretumParticipatesEsse, ParticipatedEsseHasDistinctCause, ActualContingentDependsOnActualConcretum, ExistingCauseOfActualConcretumIsConcreteGround, ActualGroundingIsSimplePriority, ActualGroundingIsDependence, DependenceForBeingAsymmetric, ActualGroundIsMoreInEsse, ActualConcrete, ActualConcreteGround, EsseCauseIsActualConcreteGround, SimplyPriorIsActualConcreteGround, NecessityCausesAreActualConcreteGrounds, EveryContingentGroundedAt, ContingentAt, LocalCausalPrinciple, ActualGroundingAsymmetric, AtMaximalTarget, IsMaximumIn, PriorityRequiresNonmutualDependence, SimplyPriorIsCauseOfBeing, MoreInIsAsymmetric, m, Control.mk, acc, ex, conc, cau, gr, C, D, P, N, Partic, More, Act]
  and_intros <;> decide

theorem asymmetricViaDependence_omit_hDep : Control.asymmetricViaDependence.omit_hDep.Holds := by
  open Control.asymmetricViaDependence.omit_hDep in
  dsimp only [Holds, EsseCausesExistAt, EsseCausesAreConcrete, EsseEffectDependsOnItsCause, ActualDependenceIsGrounding, SimplePriorityRelatesActualConcreta, NecessityCauseCausesEsse, NecessityCauseRelataActualConcrete, NecessitatedDependsOnItsCause, ContingentConcretumParticipatesEsse, ParticipatedEsseHasDistinctCause, ActualContingentDependsOnActualConcretum, ExistingCauseOfActualConcretumIsConcreteGround, ActualGroundingIsSimplePriority, ActualGroundingIsDependence, DependenceForBeingAsymmetric, ActualGroundIsMoreInEsse, ActualConcrete, ActualConcreteGround, EsseCauseIsActualConcreteGround, SimplyPriorIsActualConcreteGround, NecessityCausesAreActualConcreteGrounds, EveryContingentGroundedAt, ContingentAt, LocalCausalPrinciple, ActualGroundingAsymmetric, AtMaximalTarget, IsMaximumIn, PriorityRequiresNonmutualDependence, SimplyPriorIsCauseOfBeing, MoreInIsAsymmetric, m, Control.mk, acc, ex, conc, cau, gr, C, D, P, N, Partic, More, Act]
  and_intros <;> decide

theorem asymmetricViaDependence_omit_hAsym : Control.asymmetricViaDependence.omit_hAsym.Holds := by
  open Control.asymmetricViaDependence.omit_hAsym in
  dsimp only [Holds, EsseCausesExistAt, EsseCausesAreConcrete, EsseEffectDependsOnItsCause, ActualDependenceIsGrounding, SimplePriorityRelatesActualConcreta, NecessityCauseCausesEsse, NecessityCauseRelataActualConcrete, NecessitatedDependsOnItsCause, ContingentConcretumParticipatesEsse, ParticipatedEsseHasDistinctCause, ActualContingentDependsOnActualConcretum, ExistingCauseOfActualConcretumIsConcreteGround, ActualGroundingIsSimplePriority, ActualGroundingIsDependence, DependenceForBeingAsymmetric, ActualGroundIsMoreInEsse, ActualConcrete, ActualConcreteGround, EsseCauseIsActualConcreteGround, SimplyPriorIsActualConcreteGround, NecessityCausesAreActualConcreteGrounds, EveryContingentGroundedAt, ContingentAt, LocalCausalPrinciple, ActualGroundingAsymmetric, AtMaximalTarget, IsMaximumIn, PriorityRequiresNonmutualDependence, SimplyPriorIsCauseOfBeing, MoreInIsAsymmetric, m, Control.mk, acc, ex, conc, cau, gr, C, D, P, N, Partic, More, Act]
  and_intros <;> decide

theorem asymmetricViaGrades_omit_hMore : Control.asymmetricViaGrades.omit_hMore.Holds := by
  open Control.asymmetricViaGrades.omit_hMore in
  dsimp only [Holds, EsseCausesExistAt, EsseCausesAreConcrete, EsseEffectDependsOnItsCause, ActualDependenceIsGrounding, SimplePriorityRelatesActualConcreta, NecessityCauseCausesEsse, NecessityCauseRelataActualConcrete, NecessitatedDependsOnItsCause, ContingentConcretumParticipatesEsse, ParticipatedEsseHasDistinctCause, ActualContingentDependsOnActualConcretum, ExistingCauseOfActualConcretumIsConcreteGround, ActualGroundingIsSimplePriority, ActualGroundingIsDependence, DependenceForBeingAsymmetric, ActualGroundIsMoreInEsse, ActualConcrete, ActualConcreteGround, EsseCauseIsActualConcreteGround, SimplyPriorIsActualConcreteGround, NecessityCausesAreActualConcreteGrounds, EveryContingentGroundedAt, ContingentAt, LocalCausalPrinciple, ActualGroundingAsymmetric, AtMaximalTarget, IsMaximumIn, PriorityRequiresNonmutualDependence, SimplyPriorIsCauseOfBeing, MoreInIsAsymmetric, m, Control.mk, acc, ex, conc, cau, gr, C, D, P, N, Partic, More, Act]
  and_intros <;> decide

theorem asymmetricViaGrades_omit_hAsym : Control.asymmetricViaGrades.omit_hAsym.Holds := by
  open Control.asymmetricViaGrades.omit_hAsym in
  dsimp only [Holds, EsseCausesExistAt, EsseCausesAreConcrete, EsseEffectDependsOnItsCause, ActualDependenceIsGrounding, SimplePriorityRelatesActualConcreta, NecessityCauseCausesEsse, NecessityCauseRelataActualConcrete, NecessitatedDependsOnItsCause, ContingentConcretumParticipatesEsse, ParticipatedEsseHasDistinctCause, ActualContingentDependsOnActualConcretum, ExistingCauseOfActualConcretumIsConcreteGround, ActualGroundingIsSimplePriority, ActualGroundingIsDependence, DependenceForBeingAsymmetric, ActualGroundIsMoreInEsse, ActualConcrete, ActualConcreteGround, EsseCauseIsActualConcreteGround, SimplyPriorIsActualConcreteGround, NecessityCausesAreActualConcreteGrounds, EveryContingentGroundedAt, ContingentAt, LocalCausalPrinciple, ActualGroundingAsymmetric, AtMaximalTarget, IsMaximumIn, PriorityRequiresNonmutualDependence, SimplyPriorIsCauseOfBeing, MoreInIsAsymmetric, m, Control.mk, acc, ex, conc, cau, gr, C, D, P, N, Partic, More, Act]
  and_intros <;> decide

theorem atMaximalTargetViaGrades_omit_hMore : Control.atMaximalTargetViaGrades.omit_hMore.Holds := by
  open Control.atMaximalTargetViaGrades.omit_hMore in
  dsimp only [Holds, EsseCausesExistAt, EsseCausesAreConcrete, EsseEffectDependsOnItsCause, ActualDependenceIsGrounding, SimplePriorityRelatesActualConcreta, NecessityCauseCausesEsse, NecessityCauseRelataActualConcrete, NecessitatedDependsOnItsCause, ContingentConcretumParticipatesEsse, ParticipatedEsseHasDistinctCause, ActualContingentDependsOnActualConcretum, ExistingCauseOfActualConcretumIsConcreteGround, ActualGroundingIsSimplePriority, ActualGroundingIsDependence, DependenceForBeingAsymmetric, ActualGroundIsMoreInEsse, ActualConcrete, ActualConcreteGround, EsseCauseIsActualConcreteGround, SimplyPriorIsActualConcreteGround, NecessityCausesAreActualConcreteGrounds, EveryContingentGroundedAt, ContingentAt, LocalCausalPrinciple, ActualGroundingAsymmetric, AtMaximalTarget, IsMaximumIn, PriorityRequiresNonmutualDependence, SimplyPriorIsCauseOfBeing, MoreInIsAsymmetric, m, Control.mk, acc, ex, conc, cau, gr, C, D, P, N, Partic, More, Act]
  and_intros <;> decide

theorem witness : Control.witness.Holds := by
  open Control.witness in
  dsimp only [Holds, EsseCausesExistAt, EsseCausesAreConcrete, EsseEffectDependsOnItsCause, ActualDependenceIsGrounding, SimplePriorityRelatesActualConcreta, NecessityCauseCausesEsse, NecessityCauseRelataActualConcrete, NecessitatedDependsOnItsCause, ContingentConcretumParticipatesEsse, ParticipatedEsseHasDistinctCause, ActualContingentDependsOnActualConcretum, ExistingCauseOfActualConcretumIsConcreteGround, ActualGroundingIsSimplePriority, ActualGroundingIsDependence, DependenceForBeingAsymmetric, ActualGroundIsMoreInEsse, ActualConcrete, ActualConcreteGround, EsseCauseIsActualConcreteGround, SimplyPriorIsActualConcreteGround, NecessityCausesAreActualConcreteGrounds, EveryContingentGroundedAt, ContingentAt, LocalCausalPrinciple, ActualGroundingAsymmetric, AtMaximalTarget, IsMaximumIn, PriorityRequiresNonmutualDependence, SimplyPriorIsCauseOfBeing, MoreInIsAsymmetric, m, Control.mk, acc, ex, conc, cau, gr, C, D, P, N, Partic, More, Act]
  and_intros <;> decide

/-- Omission of restricted well-foundedness: every actual pair grounds each other,
so asymmetry fails, and well-foundedness fails because it would give asymmetry. -/
theorem wf_Holds : Control.wf.Holds := by
  have hNot : ¬ ActualGroundingAsymmetric Control.wf.m true := by
    open Control.wf in
    dsimp only [ActualGroundingAsymmetric, ActualConcrete, m, Control.mk, acc, ex, conc, cau, gr]
    decide
  exact ⟨fun h => hNot (actualGroundingAsymmetricOfWF _ _ h), hNot⟩

/-- The batch controls. -/
theorem controls : TruthCore.Causality.Round2Grounding.Control.Certificate :=
  ⟨wf_Holds,
   esseCauseGroundViaDependence_omit_hGround,
   esseCauseGroundViaDependence_omit_hExists,
   esseCauseGroundViaDependence_omit_hConcrete,
   esseCauseGroundViaDependence_omit_hDep,
   simplyPriorGroundViaDependence_omit_hReq,
   simplyPriorGroundViaDependence_omit_hRel,
   simplyPriorGroundViaDependence_omit_hGround,
   simplyPriorGroundViaEsseCause_omit_hCause,
   simplyPriorGroundViaEsseCause_omit_hRel,
   simplyPriorGroundViaEsseCause_omit_hEsse,
   necessityCauseGroundViaEsseCause_omit_hCause,
   necessityCauseGroundViaEsseCause_omit_hRel,
   necessityCauseGroundViaEsseCause_omit_hEsse,
   necessityCauseGroundViaDependence_omit_hDep,
   necessityCauseGroundViaDependence_omit_hRel,
   necessityCauseGroundViaDependence_omit_hGround,
   contingentGroundedViaParticipation_omit_hPart,
   contingentGroundedViaParticipation_omit_hCause,
   contingentGroundedViaParticipation_omit_hEsse,
   contingentGroundedViaLocalCause_omit_hLocal,
   contingentGroundedViaLocalCause_omit_hBridge,
   contingentGroundedViaDependence_omit_hDep,
   contingentGroundedViaDependence_omit_hGround,
   asymmetricViaPriority_omit_hPrior,
   asymmetricViaPriority_omit_hReq,
   asymmetricViaDependence_omit_hDep,
   asymmetricViaDependence_omit_hAsym,
   asymmetricViaGrades_omit_hMore,
   asymmetricViaGrades_omit_hAsym,
   atMaximalTargetViaGrades_omit_hMore,
   witness⟩

end TruthCore.Results.Causality.Round2Grounding
