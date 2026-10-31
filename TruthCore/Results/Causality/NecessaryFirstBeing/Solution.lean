import TruthCore.Causality.NecessaryFirstBeing
import TruthCore.Results.Causality.WholeRosterFoundation.Solution
import TruthCore.Results.Aquinas.SummaTheologiae.FirstBeingNoPotency.Solution

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
  obtain ⟨n, hr, hn⟩ := WholeRosterFoundation.necessaryActualRoot m w hPop hWhole hDep hEM
  refine ⟨n, hr, hn, ?_⟩
  intro y hy
  rcases hEM (y = n) with hEq | hNe
  · exact hEq
  · exact (hr.2 y (hPrior y n hNe hy)).elim

theorem necessaryFirstPureAct {W B Respect : Type} (m : Profile W B) (w : W)
    (PriorSimply : B → B → Prop) (InAct InPotency : B → Respect → Prop)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w)
    (hWhole : WholeRosterNotTrapped m w)
    (hDep : EveryContingentGroundedAt m w) (hEM : ExcludedMiddle)
    (hPrior : SimplyPriorIsActualConcreteGround m w PriorSimply)
    (hActPrior : ActSimplyPriorToPotencyReading InAct InPotency PriorSimply)
    (hNotBoth : NotActAndPotencyInSameRespectReading InAct InPotency) :
    NecessaryActualFirstPureActAt m w PriorSimply InPotency := by
  obtain ⟨n, hr, hn, hFirst⟩ := necessaryFirst m w PriorSimply hPop hWhole hDep hEM hPrior
  exact ⟨n, hr, hn, hFirst,
    TruthCore.Results.Aquinas.SummaTheologiae.FirstBeingNoPotency.firstBeingNoPotency
      InPotency InAct PriorSimply hActPrior hNotBoth n hFirst⟩

end TruthCore.Results.Causality.NecessaryFirstBeing
