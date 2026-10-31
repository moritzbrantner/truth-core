import TruthCore.Causality.NecessaryFirstBeing
import TruthCore.Causality.WholeRosterFoundation

namespace TruthCore.Results.Causality.NecessaryFirstBeing
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryConcreteRouteBridge
open TruthCore.Causality.WholeRosterFoundation
open TruthCore.Causality.NecessaryFirstBeing
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)
open TruthCore.Latin.Aquinas.SummaTheologiae

theorem necessaryFirst {W B : Type} (m : Profile W B) (w : W)
    (PriorSimply : B → B → Prop)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w)
    (hWhole : WholeRosterNotTrapped m w)
    (hDep : EveryContingentGroundedAt m w) (hEM : ExcludedMiddle)
    (hPrior : SimplyPriorIsActualConcreteGround m w PriorSimply) :
    NecessaryActualFirstAt m w PriorSimply := by
  sorry

theorem necessaryFirstPureAct {W B Respect : Type} (m : Profile W B) (w : W)
    (PriorSimply : B → B → Prop) (InAct InPotency : B → Respect → Prop)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w)
    (hWhole : WholeRosterNotTrapped m w)
    (hDep : EveryContingentGroundedAt m w) (hEM : ExcludedMiddle)
    (hPrior : SimplyPriorIsActualConcreteGround m w PriorSimply)
    (hActPrior : ActSimplyPriorToPotencyReading InAct InPotency PriorSimply)
    (hNotBoth : NotActAndPotencyInSameRespectReading InAct InPotency) :
    NecessaryActualFirstPureActAt m w PriorSimply InPotency := by
  sorry

end TruthCore.Results.Causality.NecessaryFirstBeing
