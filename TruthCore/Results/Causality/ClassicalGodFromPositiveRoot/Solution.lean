import TruthCore.Causality.NecessaryClassicalGodRoot
import TruthCore.Logic.ExcludedMiddle
import TruthCore.Results.Aquinas.SummaTheologiae.FirstBeingNoPotency.Solution
namespace TruthCore.Results.Causality.ClassicalGodFromPositiveRoot
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
/-- Assembly preserving ONE supplied positive-root witness through the
existing pointwise attributes and naming interfaces. Root esse actuality comes
from its supplied maximum; no global existence-to-act policy is assumed. -/
theorem derive {W Principle Respect : Type} (σ : Signature)
    (m : Profile W σ.Being) (w : W)
    (p : PrimaPars.Question3.Article4.Profile σ.Being Principle Respect)
    (GoodIn InPotency : σ.Being → Respect → Prop) (MoreIn : Respect → σ.Being → σ.Being → Prop)
    (PriorSimply ComponentOf : σ.Being → σ.Being → Prop)
    (Composite MatterForm Infinite Eternal HasIntellect HasWill : σ.Being → Prop)
    (hPositiveRoot : TruthCore.Causality.RootPositiveIntellectWill.NecessaryPositiveRootIntellectWillAt
      m w p GoodIn MoreIn PriorSimply ComponentOf Composite MatterForm HasIntellect HasWill)
    (hEM : ExcludedMiddle)
    (hGenus : MaximumInBeingCausesAllBeingsReading p.InAct MoreIn p.CausesIn p.esse)
    (hEsse : EsseCauseIsActualConcreteGround m w p.CausesIn p.esse)
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
    hPositiveRoot
  have hMax := hPositive.2.2.2.1
  have hIdent : ∀ y, IsMaximumIn p.InAct MoreIn p.esse y → y = n := by
    intro y hy
    rcases hEM (y = n) with hEq | hNe
    · exact hEq
    · have hCause := hGenus y hy n (fun h => hNe h.symm) hMax.1
      exact (hPositive.1.2 y (hEsse y n hNe hPositive.1.1 hCause)).elim
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
end TruthCore.Results.Causality.ClassicalGodFromPositiveRoot
