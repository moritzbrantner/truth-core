import TruthCore.Causality.RootPositiveIntellectWill
import TruthCore.Results.Causality.DirectEsseRootPerfectionGoodness.Solution
namespace TruthCore.Results.Causality.RootPositiveIntellectWill
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryConcreteRouteBridge
open TruthCore.Causality.ExistenceActuality
open TruthCore.Causality.WholeRosterFoundation
open TruthCore.Causality.DirectEsseRootUniquenessAtBeing
open TruthCore.Causality.RootPositiveIntellectWill
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism
open TruthCore.Logic
open TruthCore.Logic.CogitoConcrete
theorem derive {W B Principle Respect : Type} (m : Profile W B) (w : W)
    (p : PrimaPars.Question3.Article4.Profile B Principle Respect)
    (GoodIn : B → Respect → Prop) (MoreIn : Respect → B → B → Prop)
    (PriorSimply ComponentOf : B → B → Prop)
    (Composite MatterForm HasIntellect HasWill : B → Prop)
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
    (hWill : WillFollowsIntellectReading HasIntellect HasWill) :
    NecessaryPositiveRootIntellectWillAt m w p GoodIn MoreIn PriorSimply ComponentOf
      Composite MatterForm HasIntellect HasWill := by
  obtain ⟨n, hPositive, hGood⟩ :=
    TruthCore.Results.Causality.DirectEsseRootPerfectionGoodness.derive
      m w p.InAct GoodIn MoreIn p.CausesIn p.esse hPop hWhole hDep hEM hGenus
      hExisting hEsse hApproach hBeing hPreexist hGoodness hTransfer
  have hr := hPositive.1
  have hSimple : IsSimple Composite n := by
    intro hc
    obtain ⟨c, hne, hCause⟩ := hUniting n hc
    exact hr.2 c (hEsse c n hne hr.1 hCause)
  have hFirst : IsFirstBeing PriorSimply n := by
    intro y hy
    rcases hEM (y = n) with hEq | hNe
    · exact hEq
    · exact (hr.2 y (hPrior y n hNe hy)).elim
  have hIdentity : p.esseOf n = p.essenceOf n := by
    rcases hEM (p.esseOf n = p.essenceOf n) with hEq | hNe
    · exact hEq
    · exact (hSimple ((hKinds n).2 hNe)).elim
  have hMatter : ¬ MatterForm n := fun h => hSimple ((hKinds n).1 h)
  have hRemote : RemoteFromAll ComponentOf n := fun y hy => hNoComponent n y hy hFirst
  have hInt := hIntellect n hMatter hRemote
  exact ⟨n, hPositive, hGood, hIdentity, hSimple, hFirst, hMatter, hRemote,
    hInt, hWill n hInt⟩
end TruthCore.Results.Causality.RootPositiveIntellectWill
