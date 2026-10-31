import TruthCore.Causality.NecessaryFirstAttributes
import TruthCore.Causality.WholeRosterFoundation

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
  sorry

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
  sorry

end TruthCore.Results.Causality.NecessaryFirstAttributes
