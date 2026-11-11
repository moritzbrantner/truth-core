module

public import TruthCore.Causality.NecessaryClassicalGodRoot
public import TruthCore.Causality.NecessaryConcreteUnderived
public import TruthCore.Logic.ExcludedMiddle
public import TruthCore.Case.Catholicism.ClassicalAttributesLocalLogic
public import TruthCore.Results.Causality.NecessaryClassicalGodRootFromUnderived.Solution

/-! Registration wrapper for the join-to-stage-two composition
(`NecessaryClassicalGodRootFromUnderived.derive`). Its only change is the head of
the act-priority hypothesis: the transparent wrapper
`ClassicalAttributesLocalLogic.IndependentPriority`, whose body is exactly
`ActSimplyPriorToPotencyReading`, binds that hypothesis to the analyst record for
act priority over the independently supplied potency parameter (statement
3b2d2d46-baa6-4772-a2db-bb3daeb092fc, POTENCY_CAPACITY_AND_POWER_ACROSS_ADOPTED_2).
Every potency occurrence in this theorem is the same free `InPotency`; no
capacity-without-act equation (adopted POTENCY_1) is assumed or crossed. The same
device registered ClassicalAttributesLocalLogic (#1278). No premise, axiom or
bridge is added: the proof is the original composition, by definitional unfolding. -/

@[expose] public section

namespace TruthCore.Results.Causality.NecessaryClassicalGodRootFromUnderived.Registration
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryConcreteRouteBridge
open TruthCore.Causality.ExistenceActuality
open TruthCore.Causality.DirectEsseRootUniquenessAtBeing
open TruthCore.Causality.NecessaryConcreteUnderived
open TruthCore.Causality.NecessaryClassicalGodRoot
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism
open TruthCore.Logic
theorem derive {W Principle Respect : Type} (σ : Signature)
    (m : Profile W σ.Being) (w : W)
    (p : PrimaPars.Question3.Article4.Profile σ.Being Principle Respect)
    (GoodIn InPotency : σ.Being → Respect → Prop) (MoreIn : Respect → σ.Being → σ.Being → Prop)
    (PriorSimply ComponentOf : σ.Being → σ.Being → Prop)
    (Composite MatterForm Infinite Eternal HasIntellect HasWill : σ.Being → Prop)
    (hUnderived : NecessaryConcreteUnderivedAt m w) (hEM : ExcludedMiddle)
    (hGenus : MaximumInBeingCausesAllBeingsReading p.InAct MoreIn p.CausesIn p.esse)
    (hExisting : ExistingInActAt m.ontic p.InAct p.esse w)
    (hEsse : EsseCauseIsActualConcreteGround m w p.CausesIn p.esse)
    (hApproach : GradesToMaximumAtBeing p.InAct MoreIn p.esse)
    (hBeing : ActualityOnlyInsofarAsBeingReading p.InAct p.esse)
    (hPreexist : PerfectionsOfEffectPreexistInCauseReading p.InAct p.CausesIn p.esse)
    (hGoodness : GoodnessIsActualityReading GoodIn p.InAct)
    (hTransfer : UniversalCauseTransfersPerfections p.InAct p.CausesIn p.esse)
    (hUniting : CompositeHasAUnitingCauseReading Composite p.CausesIn p.esse)
    (hKinds : MatterFormAndEsseEssenceAreCompositionsReading MatterForm Composite p.essenceOf p.esseOf)
    (hPrior : SimplyPriorIsActualConcreteGround m w PriorSimply)
    (hNoComponent : NoComponentIsFirstBeingReading ComponentOf PriorSimply)
    (hIntellect : ImmaterialIsIntellectualReading MatterForm HasIntellect ComponentOf)
    (hWill : WillFollowsIntellectReading HasIntellect HasWill)
    (hActPrior : TruthCore.Case.Catholicism.ClassicalAttributesLocalLogic.IndependentPriority
      p.InAct InPotency PriorSimply)
    (hNotBoth : NotActAndPotencyInSameRespectReading p.InAct InPotency)
    (hInfinity : SubsistentBeingIsInfiniteReading p.essenceOf p.esseOf Infinite)
    (hEternity : ImmutableIsEternalReading InPotency Eternal)
    (hNaming : GodNamesTheFullyDescribedPrinciple p.InAct MoreIn p.CausesIn p.esse ComponentOf σ.IsGod)
    (hGodMaximal : GodIsMaximalInBeing σ.IsGod p.InAct MoreIn p.esse)
    (hSuffice : ClassicalAttributesSuffice σ (IsSimple Composite) (IsPerfect p.InAct)
      (IsSupremelyGood p.InAct GoodIn p.CausesIn p.esse) (IsTheOneGod σ.IsGod)
      Infinite (IsImmutable InPotency) Eternal HasIntellect HasWill) :
    NecessaryClassicalGodRootAt σ m w p GoodIn InPotency MoreIn PriorSimply ComponentOf
      Composite MatterForm Infinite Eternal HasIntellect HasWill := by
  exact TruthCore.Results.Causality.NecessaryClassicalGodRootFromUnderived.derive
    σ m w p GoodIn InPotency MoreIn PriorSimply ComponentOf Composite MatterForm
    Infinite Eternal HasIntellect HasWill hUnderived hEM hGenus hExisting hEsse hApproach
    hBeing hPreexist hGoodness hTransfer hUniting hKinds hPrior hNoComponent hIntellect hWill
    hActPrior hNotBoth hInfinity hEternity hNaming hGodMaximal hSuffice
end TruthCore.Results.Causality.NecessaryClassicalGodRootFromUnderived.Registration
