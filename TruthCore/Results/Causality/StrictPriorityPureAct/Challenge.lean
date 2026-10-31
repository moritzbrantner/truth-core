import TruthCore.Causality.StrictPriorityPureAct
namespace TruthCore.Results.Causality.StrictPriorityPureAct
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.WholeRosterFoundation
open TruthCore.Causality.NecessaryConcreteRouteBridge
open TruthCore.Causality.NecessaryFirstBeing
open TruthCore.Causality.StrictPriorityPureAct
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)
theorem necessaryFirstPureAct {W B Respect : Type} (m : Profile W B) (w : W)
    (PriorSimply : B → B → Prop) (InAct InPotency : B → Respect → Prop)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w)
    (hWhole : WholeRosterNotTrapped m w)
    (hDep : EveryContingentGroundedAt m w) (hEM : ExcludedMiddle)
    (hPrior : SimplyPriorIsActualConcreteGround m w PriorSimply)
    (hActPrior : ActSimplyPriorToPotencyReading InAct InPotency PriorSimply)
    (hStrict : StrictSimplePriority PriorSimply) :
    NecessaryActualFirstPureActAt m w PriorSimply InPotency := by
  sorry
end TruthCore.Results.Causality.StrictPriorityPureAct
