import TruthCore.Causality.DirectEsseRootRoute
import TruthCore.Causality.NecessaryRootUniqueness
import TruthCore.Results.Causality.WholeRosterFoundation.Solution

namespace TruthCore.Results.Causality.DirectEsseRootUniqueness
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.DirectEsseRootRoute
open TruthCore.Causality.NecessaryConcreteRouteBridge
open TruthCore.Causality.ExistenceActuality (ExistingInActAt)
open TruthCore.Causality.NecessaryRootUniqueness
open TruthCore.Causality.WholeRosterFoundation
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)

theorem uniqueRoot {W B Respect : Type} (m : Profile W B) (w : W)
    (InAct : B → Respect → Prop) (MoreIn : Respect → B → B → Prop)
    (CausesIn : B → B → Respect → Prop) (esse : Respect)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w)
    (hWhole : WholeRosterNotTrapped m w)
    (hDep : EveryContingentGroundedAt m w) (hEM : ExcludedMiddle)
    (hGenus : MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn)
    (hExisting : ExistingInActAt m.ontic InAct esse w)
    (hEsse : EsseCauseIsActualConcreteGround m w CausesIn esse)
    (hApproach : GradesByApproachToAMaximumReading InAct MoreIn) :
    UniqueNecessaryActualRootAt m w := by
  obtain ⟨n, hr, hn⟩ := WholeRosterFoundation.necessaryActualRoot m w hPop hWhole hDep hEM
  obtain ⟨_, _, hCommon⟩ := necessaryRootCommonGround m w InAct MoreIn CausesIn esse n
    hr hn hEM hGenus hExisting hEsse hApproach
  refine ⟨n, hr, hn, ?_⟩
  intro x hx
  rcases hEM (x = n) with h | h
  · exact h
  · exact (hx.2 n (hCommon x hx.1 h)).elim

end TruthCore.Results.Causality.DirectEsseRootUniqueness
