import TruthCore.Causality.NecessaryFirstAttributes
import TruthCore.Results.Causality.NecessaryFirstBeing.Solution

namespace TruthCore.Results.Causality.NecessaryFirstAttributes
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryConcreteRouteBridge
open TruthCore.Causality.WholeRosterFoundation
open TruthCore.Causality.NecessaryFirstBeing
open TruthCore.Causality.NecessaryFirstAttributes
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)
open TruthCore.Latin.Aquinas.SummaTheologiae

theorem attributesFromFirst {W B Respect : Type} (m : Profile W B) (w : W)
    (PriorSimply ComponentOf : B → B → Prop)
    (InPotency : B → Respect → Prop) (Composite : B → Prop)
    (hFirst : NecessaryActualFirstPureActAt m w PriorSimply InPotency)
    (hPosterior : CompositePosteriorToComponentsReading ComponentOf PriorSimply)
    (hOther : CompositeHasComponentOtherThanItselfReading Composite ComponentOf)
    (hNoComponent : NoComponentIsFirstBeingReading ComponentOf PriorSimply) :
    NecessaryFirstAttributesAt m w PriorSimply ComponentOf InPotency Composite := by
  obtain ⟨n, hRoot, hNecessary, hFirst, hPure⟩ := hFirst
  have hNoncomposite : ¬ Composite n := by
    intro hComposite
    obtain ⟨p, hComponent, hDistinct⟩ := hOther n hComposite
    exact hDistinct (hFirst p (hPosterior p n hComponent))
  exact ⟨n, hRoot, hNecessary, hFirst, hPure, hNoncomposite,
    fun x hComponent => hNoComponent n x hComponent hFirst⟩

theorem attributesFromWhole {W B Respect : Type} (m : Profile W B) (w : W)
    (PriorSimply ComponentOf : B → B → Prop)
    (InAct InPotency : B → Respect → Prop) (Composite : B → Prop)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w)
    (hWhole : WholeRosterNotTrapped m w)
    (hDep : EveryContingentGroundedAt m w) (hEM : ExcludedMiddle)
    (hPrior : SimplyPriorIsActualConcreteGround m w PriorSimply)
    (hActPrior : ActSimplyPriorToPotencyReading InAct InPotency PriorSimply)
    (hNotBoth : NotActAndPotencyInSameRespectReading InAct InPotency)
    (hPosterior : CompositePosteriorToComponentsReading ComponentOf PriorSimply)
    (hOther : CompositeHasComponentOtherThanItselfReading Composite ComponentOf)
    (hNoComponent : NoComponentIsFirstBeingReading ComponentOf PriorSimply) :
    NecessaryFirstAttributesAt m w PriorSimply ComponentOf InPotency Composite := by
  exact attributesFromFirst m w PriorSimply ComponentOf InPotency Composite
    (TruthCore.Results.Causality.NecessaryFirstBeing.necessaryFirstPureAct
      m w PriorSimply InAct InPotency hPop hWhole hDep hEM hPrior hActPrior hNotBoth)
    hPosterior hOther hNoComponent

end TruthCore.Results.Causality.NecessaryFirstAttributes
