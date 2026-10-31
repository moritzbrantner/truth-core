import TruthCore.Causality.NecessaryRootUniqueness
import TruthCore.Results.Causality.WholeRosterFoundation.Solution

namespace TruthCore.Results.Causality.NecessaryRootUniqueness
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryRootFork
open TruthCore.Causality.NecessaryConcreteRouteBridge
open TruthCore.Causality.WholeRosterFoundation
open TruthCore.Causality.NecessaryRootUniqueness
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism (NecessaryBeingHasBeing CauseOfNecessaryBeingCausesItsNecessity)
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)

theorem uniqueRoot {W B Respect : Type} (m : Profile W B) (w : W)
    (CausesNecessityOf : B → B → Prop) (InAct : B → Respect → Prop)
    (MoreIn : Respect → B → B → Prop) (CausesIn : B → B → Respect → Prop)
    (esse : Respect)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w)
    (hWhole : WholeRosterNotTrapped m w)
    (hDep : EveryContingentGroundedAt m w) (hEM : ExcludedMiddle)
    (hBridge : NecessityCausesAreActualConcreteGrounds m w CausesNecessityOf)
    (hGenus : MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn)
    (hHasBeing : NecessaryBeingHasBeing (modalPossible m w) (modalIsAt m) InAct esse)
    (hCause : CauseOfNecessaryBeingCausesItsNecessity (modalPossible m w) (modalIsAt m)
      CausesIn esse CausesNecessityOf)
    (hApproach : GradesByApproachToAMaximumReading InAct MoreIn) :
    UniqueNecessaryActualRootAt m w := by
  obtain ⟨n, hRoot, hNecessary⟩ :=
    WholeRosterFoundation.necessaryActualRoot m w hPop hWhole hDep hEM
  obtain ⟨maximum, hMaximum⟩ :=
    maximumExistsOfNecessaryAt m w InAct MoreIn esse n hNecessary hHasBeing hApproach hEM
  have hIdentity := (necessaryRootIsMaximumOfRoot m w CausesNecessityOf
    InAct MoreIn CausesIn esse n hRoot hNecessary hEM hBridge hGenus hHasBeing hCause).2
  refine ⟨n, hRoot, hNecessary, ?_⟩
  intro x hXRoot
  have hXNecessary : TruthCore.German.Kant.CosmologicalInference.NecessaryAt m.ontic w x := by
    rcases hEM (TruthCore.German.Kant.CosmologicalInference.NecessaryAt m.ontic w x)
      with h | h
    · exact h
    · exact ((everyContingentGrounded_iff_noContingentRoot m w hEM).mp hDep
        (contingentRootOfNonnecessary m w hEM ⟨x, hXRoot, h⟩)).elim
  have hXIdentity := (necessaryRootIsMaximumOfRoot m w CausesNecessityOf
    InAct MoreIn CausesIn esse x hXRoot hXNecessary hEM hBridge hGenus hHasBeing hCause).2
  exact (hXIdentity maximum hMaximum).symm.trans (hIdentity maximum hMaximum)

end TruthCore.Results.Causality.NecessaryRootUniqueness
