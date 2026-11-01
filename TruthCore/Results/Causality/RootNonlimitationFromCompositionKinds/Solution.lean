import TruthCore.Results.Causality.NecessaryFirstBeing.Solution
import TruthCore.Causality.RootIntellectWill
import TruthCore.Results.Causality.RootWithoutLimitingPrinciple.Solution
import TruthCore.Results.Causality.RootEssenceIdentity.Solution

namespace TruthCore.Results.Causality.RootNonlimitationFromCompositionKinds
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
theorem necessaryRootWithoutLimitingPrinciple {W B P R : Type} (m : Profile W B) (w : W)
    (p : TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4.Profile B P R)
    (PriorSimply ComponentOf : B → B → Prop) (Composite MatterForm : B → Prop)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w)
    (hWhole : WholeRosterNotTrapped m w)
    (hDep : EveryContingentGroundedAt m w) (hEM : ExcludedMiddle)
    (hPrior : SimplyPriorIsActualConcreteGround m w PriorSimply)
    (hPosterior : CompositePosteriorToComponentsReading ComponentOf PriorSimply)
    (hOther : CompositeHasComponentOtherThanItselfReading Composite ComponentOf)
    (hKinds : MatterFormAndEsseEssenceAreCompositionsReading MatterForm Composite p.essenceOf p.esseOf) :
    NecessaryRootWithoutLimitingPrincipleAt m w p Composite PriorSimply := by
  obtain ⟨n, hr, hn, hFirst⟩ :=
    TruthCore.Results.Causality.NecessaryFirstBeing.necessaryFirst
      m w PriorSimply hPop hWhole hDep hEM hPrior
  have hNoncomposite : ¬ Composite n := by
    intro hComposite
    obtain ⟨part, hComponent, hDistinct⟩ := hOther n hComposite
    exact hDistinct (hFirst part (hPosterior part n hComponent))
  have hIdentity : p.esseOf n = p.essenceOf n := by
    rcases hEM (p.esseOf n = p.essenceOf n) with hEq | hNe
    · exact hEq
    · exact (hNoncomposite ((hKinds n).2 hNe)).elim
  refine ⟨n, hr, hn, ?_⟩
  rintro (hComposite | hDistinctEsse | ⟨y, hDistinct, hPriorY⟩)
  · exact hNoncomposite hComposite
  · exact hDistinctEsse hIdentity
  · exact hDistinct (hFirst y hPriorY)

end TruthCore.Results.Causality.RootNonlimitationFromCompositionKinds
