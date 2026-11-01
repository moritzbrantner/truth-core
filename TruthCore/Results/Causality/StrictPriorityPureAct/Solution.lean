import TruthCore.Causality.StrictPriorityPureAct
import TruthCore.Results.Causality.NecessaryFirstBeing.Solution
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
  obtain ⟨n, hr, hn, hFirst⟩ :=
    TruthCore.Results.Causality.NecessaryFirstBeing.necessaryFirst
      m w PriorSimply hPop hWhole hDep hEM hPrior
  refine ⟨n, hr, hn, hFirst, ?_⟩
  intro r hp
  obtain ⟨y, _, hy⟩ := hActPrior n r hp
  have hEq : y = n := hFirst y hy
  subst y
  exact hStrict.irrefl n hy
end TruthCore.Results.Causality.StrictPriorityPureAct
