import TruthCore.Results.Causality.NecessaryClassicalGodRootControl.Solution
import TruthCore.Results.Causality.WholeRosterFromMaximumAsymmetry.Solution
import TruthCore.Results.Causality.NecessaryClassicalGodRoot.Solution
import TruthCore.Causality.NecessaryClassicalGodRoot
import TruthCore.Results.Causality.RootPositiveIntellectWill.Solution
import TruthCore.Results.Aquinas.SummaTheologiae.FirstBeingNoPotency.Solution
namespace TruthCore.Results.Causality.NecessaryClassicalGodRootFromAsymmetry
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
    (hAsym : ActualGroundingAsymmetric m w)
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
  have hWhole := TruthCore.Results.Causality.WholeRosterFromMaximumAsymmetry.wholeRoster
    m w p.InAct MoreIn p.CausesIn p.esse hPop hExisting hEsse hGenus hApproach hEM hAsym
  exact TruthCore.Results.Causality.NecessaryClassicalGodRoot.derive
    σ m w p GoodIn InPotency MoreIn PriorSimply ComponentOf Composite MatterForm
    Infinite Eternal HasIntellect HasWill hPop hWhole hDep hEM hGenus hExisting hEsse
    hApproach hBeing hPreexist hGoodness hTransfer hUniting hKinds hPrior hNoComponent
    hIntellect hWill hActPrior hNotBoth hInfinity hEternity hNaming hGodMaximal hSuffice
/-- Closed check on the EXACT old full25 concurrent fixture, without changing
any field. This is not an additional premise of derive. -/
theorem actualGroundingAsymmetricControl : ActualGroundingAsymmetric
    TruthCore.Causality.RootPositiveIntellectWillControl.model false := by
  have h : ∀ a b : TransferRole, transferCause true a b false →
      ¬ transferCause true b a false := by
    intro a b
    cases a <;> cases b <;> decide
  intro a b _ _ hab hba
  exact h a b hab hba

/-- Compatibility with the stronger old positive background. Its incidental D
is not added back to the replacement theorem. Empty potency, finite respects,
and the necessary non-God effect retain exactly the old control's scope. -/
theorem compatibility (hEM : ExcludedMiddle) :
    TruthCore.Causality.NecessaryClassicalGodRootControl.Control ∧
    ActualGroundingAsymmetric TruthCore.Causality.RootPositiveIntellectWillControl.model false :=
  ⟨TruthCore.Results.Causality.NecessaryClassicalGodRootControl.checks hEM,
    actualGroundingAsymmetricControl⟩
end TruthCore.Results.Causality.NecessaryClassicalGodRootFromAsymmetry
