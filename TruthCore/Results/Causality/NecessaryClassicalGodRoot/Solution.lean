import TruthCore.Causality.NecessaryClassicalGodRoot
import TruthCore.Results.Causality.RootPositiveIntellectWill.Solution
import TruthCore.Results.Aquinas.SummaTheologiae.FirstBeingNoPotency.Solution
namespace TruthCore.Results.Causality.NecessaryClassicalGodRoot
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryConcreteRouteBridge
open TruthCore.Causality.ExistenceActuality
open TruthCore.Causality.WholeRosterFoundation
open TruthCore.Causality.DirectEsseRootUniquenessAtBeing
open TruthCore.Causality.NecessaryClassicalGodRoot
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism
open TruthCore.Logic
open TruthCore.Logic.CogitoConcrete
theorem derive {W Principle Respect : Type} (σ : Signature)
    (m : Profile W σ.Being) (w : W)
    (p : PrimaPars.Question3.Article4.Profile σ.Being Principle Respect)
    (GoodIn InPotency : σ.Being → Respect → Prop) (MoreIn : Respect → σ.Being → σ.Being → Prop)
    (PriorSimply ComponentOf : σ.Being → σ.Being → Prop)
    (Composite MatterForm Infinite Eternal HasIntellect HasWill : σ.Being → Prop)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w)
    (hWhole : WholeRosterNotTrapped m w)
    (hDep : EveryContingentGroundedAt m w) (hEM : ExcludedMiddle)
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
    (hActPrior : ActSimplyPriorToPotencyReading p.InAct InPotency PriorSimply)
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
  obtain ⟨n, hPositive, hGood, hIdentity, hSimple, hFirst, hMatter, hRemote, hInt, hWillN⟩ :=
    TruthCore.Results.Causality.RootPositiveIntellectWill.derive
      m w p GoodIn MoreIn PriorSimply ComponentOf Composite MatterForm HasIntellect HasWill
      hPop hWhole hDep hEM hGenus hExisting hEsse hApproach hBeing hPreexist hGoodness
      hTransfer hUniting hKinds hPrior hNoComponent hIntellect hWill
  have hMax := hPositive.2.2.2.1
  have hIdent : ∀ y, IsMaximumIn p.InAct MoreIn p.esse y → y = n :=
    TruthCore.Causality.DirectEsseRootRoute.maximumEqualsRoot
      m w (fun x (_ : Unit) => p.InAct x p.esse)
      (fun (_ : Unit) y x => MoreIn p.esse y x)
      (fun c x (_ : Unit) => p.CausesIn c x p.esse) () n hPositive.1 hEM
      (fun _ => hGenus) hExisting hEsse
  have hGod : σ.IsGod n :=
    hNaming n hMax (hGenus n hMax) hGood.2 hRemote hIdent
  have hOne : IsTheOneGod σ.IsGod n := fun g hg => hIdent g (hGodMaximal g hg)
  have hPure : PureAct InPotency n :=
    TruthCore.Results.Aquinas.SummaTheologiae.FirstBeingNoPotency.firstBeingNoPotency
      InPotency p.InAct PriorSimply hActPrior hNotBoth n hFirst
  have hInfinite := hInfinity n hIdentity
  have hEternal := hEternity n hPure
  have hNine : NineClassicalAttributes (IsSimple Composite) (IsPerfect p.InAct)
      (IsSupremelyGood p.InAct GoodIn p.CausesIn p.esse) (IsTheOneGod σ.IsGod)
      Infinite (IsImmutable InPotency) Eternal HasIntellect HasWill n :=
    ⟨hSimple, hPositive.2.2.2.2, hGood, hOne, hInfinite, hPure, hEternal, hInt, hWillN⟩
  have hField := classicalAttributesFromNine σ (IsSimple Composite) (IsPerfect p.InAct)
    (IsSupremelyGood p.InAct GoodIn p.CausesIn p.esse) (IsTheOneGod σ.IsGod)
    Infinite (IsImmutable InPotency) Eternal HasIntellect HasWill hSuffice n hNine
  exact ⟨n, hPositive, hIdentity, hFirst, hMatter, hRemote, hGod, hNine, hField⟩
end TruthCore.Results.Causality.NecessaryClassicalGodRoot
