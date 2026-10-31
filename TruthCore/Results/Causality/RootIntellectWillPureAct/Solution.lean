import TruthCore.Results.Causality.RootIntellectWillReduced.Solution
import TruthCore.Results.Aquinas.SummaTheologiae.FirstBeingNoPotency.Solution
import TruthCore.Causality.RootIntellectWillPureAct
import TruthCore.Results.Causality.RootWithoutLimitingPrinciple.Solution
import TruthCore.Results.Causality.RootEssenceIdentity.Solution

namespace TruthCore.Results.Causality.RootIntellectWillPureAct
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryConcreteRouteBridge (EsseCauseIsActualConcreteGround)
open TruthCore.Causality.ExistenceActuality (ExistingInActAt)
open TruthCore.Causality.WholeRosterFoundation
open TruthCore.Causality.RootEssenceIdentity
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4
  (DistinctEsseCauseDichotomyReading EssentialPrinciplesCannotCauseDistinctEsseReading)
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)

open TruthCore.Causality.RootWithoutLimitingPrinciple
open TruthCore.Causality.RootMultiplication (HasLimitingPrinciple)
open TruthCore.Causality.NecessaryConcreteRouteBridge (SimplyPriorIsActualConcreteGround)
open TruthCore.Latin.Aquinas.SummaTheologiae

open TruthCore.Causality.RootIntellectWill
open TruthCore.Case.Catholicism (IsSimple RemoteFromAll)
open TruthCore.Causality.RootIntellectWillPureAct
theorem necessaryRootIntellectWillPureAct {W B P R : Type} (m : Profile W B) (w : W)
    (p : TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4.Profile B P R)
    (PriorSimply ComponentOf : B → B → Prop) (Composite MatterForm HasIntellect HasWill : B → Prop)
    (InPotency : B → R → Prop)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w)
    (hWhole : WholeRosterNotTrapped m w)
    (hDep : EveryContingentGroundedAt m w) (hEM : ExcludedMiddle)
    (hPrior : SimplyPriorIsActualConcreteGround m w PriorSimply)
    (hPosterior : CompositePosteriorToComponentsReading ComponentOf PriorSimply)
    (hOther : CompositeHasComponentOtherThanItselfReading Composite ComponentOf)
    (hKinds : MatterFormAndEsseEssenceAreCompositionsReading MatterForm Composite p.essenceOf p.esseOf)
    (hNoComponent : NoComponentIsFirstBeingReading ComponentOf PriorSimply)
    (hIntellect : ImmaterialIsIntellectualReading MatterForm HasIntellect ComponentOf)
    (hWill : WillFollowsIntellectReading HasIntellect HasWill)
    (hActPrior : ActSimplyPriorToPotencyReading p.InAct InPotency PriorSimply)
    (hNotBoth : NotActAndPotencyInSameRespectReading p.InAct InPotency) :
    NecessaryRootIntellectWillPureActAt m w p PriorSimply ComponentOf Composite MatterForm HasIntellect HasWill InPotency := by
  obtain ⟨n, hr, hn, hIdentity, hSimple, hFirst, hNotMatter, hRemote, hIntellectN, hWillN⟩ :=
    TruthCore.Results.Causality.RootIntellectWillReduced.necessaryRootIntellectWill
      m w p PriorSimply ComponentOf Composite MatterForm HasIntellect HasWill
      hPop hWhole hDep hEM hPrior hPosterior hOther hKinds hNoComponent hIntellect hWill
  have hPure := TruthCore.Results.Aquinas.SummaTheologiae.FirstBeingNoPotency.firstBeingNoPotency
    InPotency p.InAct PriorSimply hActPrior hNotBoth n hFirst
  exact ⟨n, hr, hn, hIdentity, hSimple, hFirst, hNotMatter, hRemote, hIntellectN, hWillN, hPure⟩

end TruthCore.Results.Causality.RootIntellectWillPureAct
