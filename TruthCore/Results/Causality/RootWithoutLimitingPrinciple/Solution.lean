import TruthCore.Causality.RootWithoutLimitingPrinciple
import TruthCore.Results.Causality.RootEssenceIdentity.Solution

namespace TruthCore.Results.Causality.RootWithoutLimitingPrinciple
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

theorem necessaryRootWithoutLimitingPrinciple {W B P R : Type} (m : Profile W B) (w : W)
    (p : TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4.Profile B P R)
    (PriorSimply ComponentOf : B → B → Prop) (Composite : B → Prop)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w)
    (hWhole : WholeRosterNotTrapped m w)
    (hDep : EveryContingentGroundedAt m w) (hEM : ExcludedMiddle)
    (hExisting : ExistingInActAt m.ontic p.InAct p.esse w)
    (hEsse : EsseCauseIsActualConcreteGround m w p.CausesIn p.esse)
    (hExhaustive : DistinctEsseCauseDichotomyReading p)
    (hNoSelfCause : EssentialPrinciplesCannotCauseDistinctEsseReading p)
    (hPrior : SimplyPriorIsActualConcreteGround m w PriorSimply)
    (hPosterior : CompositePosteriorToComponentsReading ComponentOf PriorSimply)
    (hOther : CompositeHasComponentOtherThanItselfReading Composite ComponentOf) :
    NecessaryRootWithoutLimitingPrincipleAt m w p Composite PriorSimply := by
  obtain ⟨n, hr, hn, hIdentity⟩ :=
    TruthCore.Results.Causality.RootEssenceIdentity.necessaryRootIdentity
      m w p hPop hWhole hDep hEM hExisting hEsse hExhaustive hNoSelfCause
  have hFirst : IsFirstBeing PriorSimply n := by
    intro y hy
    rcases hEM (y = n) with hEq | hNe
    · exact hEq
    · exact (hr.2 y (hPrior y n hNe hy)).elim
  have hNoncomposite : ¬ Composite n := by
    intro hComposite
    obtain ⟨part, hComponent, hDistinct⟩ := hOther n hComposite
    exact hDistinct (hFirst part (hPosterior part n hComponent))
  refine ⟨n, hr, hn, ?_⟩
  intro hLimited
  rcases hLimited with hComposite | hDistinctEsse | ⟨y, hDistinct, hPriorY⟩
  · exact hNoncomposite hComposite
  · exact hDistinctEsse hIdentity
  · exact hDistinct (hFirst y hPriorY)

end TruthCore.Results.Causality.RootWithoutLimitingPrinciple
