import TruthCore.Causality.RootIntellectWill
import TruthCore.Results.Causality.RootWithoutLimitingPrinciple.Solution
import TruthCore.Results.Causality.RootEssenceIdentity.Solution

namespace TruthCore.Results.Causality.RootIntellectWill
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
theorem necessaryRootIntellectWill {W B P R : Type} (m : Profile W B) (w : W)
    (p : TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4.Profile B P R)
    (PriorSimply ComponentOf : B → B → Prop) (Composite MatterForm HasIntellect HasWill : B → Prop)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w)
    (hWhole : WholeRosterNotTrapped m w)
    (hDep : EveryContingentGroundedAt m w) (hEM : ExcludedMiddle)
    (hExisting : ExistingInActAt m.ontic p.InAct p.esse w)
    (hEsse : EsseCauseIsActualConcreteGround m w p.CausesIn p.esse)
    (hExhaustive : DistinctEsseCauseDichotomyReading p)
    (hNoSelfCause : EssentialPrinciplesCannotCauseDistinctEsseReading p)
    (hPrior : SimplyPriorIsActualConcreteGround m w PriorSimply)
    (hPosterior : CompositePosteriorToComponentsReading ComponentOf PriorSimply)
    (hOther : CompositeHasComponentOtherThanItselfReading Composite ComponentOf)
    (hKinds : MatterFormAndEsseEssenceAreCompositionsReading MatterForm Composite p.essenceOf p.esseOf)
    (hNoComponent : NoComponentIsFirstBeingReading ComponentOf PriorSimply)
    (hIntellect : ImmaterialIsIntellectualReading MatterForm HasIntellect ComponentOf)
    (hWill : WillFollowsIntellectReading HasIntellect HasWill) :
    NecessaryRootIntellectWillAt m w p PriorSimply ComponentOf Composite MatterForm HasIntellect HasWill := by
  obtain ⟨n, hr, hn, hNoLimit⟩ :=
    TruthCore.Results.Causality.RootWithoutLimitingPrinciple.necessaryRootWithoutLimitingPrinciple
      m w p PriorSimply ComponentOf Composite hPop hWhole hDep hEM hExisting hEsse
      hExhaustive hNoSelfCause hPrior hPosterior hOther
  have hSimple : IsSimple Composite n := fun h => hNoLimit (Or.inl h)
  have hFirst : IsFirstBeing PriorSimply n := by
    intro y hy
    rcases hEM (y = n) with hEq | hNe
    · exact hEq
    · exact (hNoLimit (Or.inr (Or.inr ⟨y, hNe, hy⟩))).elim
  have hIdentity : p.esseOf n = p.essenceOf n := by
    rcases hEM (p.esseOf n = p.essenceOf n) with hEq | hNe
    · exact hEq
    · exact (hNoLimit (Or.inr (Or.inl hNe))).elim
  have hNotMatter : ¬ MatterForm n := fun h => hSimple ((hKinds n).1 h)
  have hRemote : RemoteFromAll ComponentOf n :=
    fun y hy => hNoComponent n y hy hFirst
  have hUnderstanding := hIntellect n hNotMatter hRemote
  exact ⟨n, hr, hn, hIdentity, hSimple, hFirst, hNotMatter, hRemote,
    hUnderstanding, hWill n hUnderstanding⟩

end TruthCore.Results.Causality.RootIntellectWill
