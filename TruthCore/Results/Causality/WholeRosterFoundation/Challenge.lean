import TruthCore.Causality.WholeRosterFoundation
import TruthCore.Causality.NecessaryConcreteRouteBridge

namespace TruthCore.Results.Causality.WholeRosterFoundation
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryRootFork
open TruthCore.Causality.ConcreteExistentialSupply
open TruthCore.Causality.NecessaryConcreteRouteBridge
open TruthCore.Causality.WholeRosterFoundation
open TruthCore.Causality.JointGroups
open TruthCore.Causality.DerivativeJointPower
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)
open TruthCore.Latin.Aquinas.SummaTheologiae (MaximumInGenusCausesAllInGenusReading)
open TruthCore.Case.Catholicism (MaximumInBeingIsFirstBeing NecessaryBeingHasBeing
  CauseOfNecessaryBeingCausesItsNecessity)

/-- The existing all-subsets cut implies its whole-roster restriction. -/
theorem wholeRosterOfBorrowingEscape {W B : Type} (m : Profile W B) (w : W)
    (hEscape : ActualConcreteBorrowingEscape m w) : WholeRosterNotTrapped m w := by
  sorry

/-- Whole-roster nontrapping, actual population and contingent dependence give
an actual necessary concretum. No all-subsets cut or WF premise is used. -/
theorem necessaryConcrete {W B : Type} (m : Profile W B) (w : W)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w)
    (hWhole : WholeRosterNotTrapped m w)
    (hDep : EveryContingentGroundedAt m w) (hEM : ExcludedMiddle) :
    NecessaryConcreteAt m w := by
  sorry

/-- The same necessary root feeds the existing per-se/convergence proof and
simply-prior bridge. No maximum existence or full explanatory completion follows. -/
theorem maximumFirst {W B Respect : Type} (m : Profile W B) (w : W)
    (CausesNecessityOf : B → B → Prop) (InAct : B → Respect → Prop)
    (MoreIn : Respect → B → B → Prop) (CausesIn : B → B → Respect → Prop)
    (PriorSimply : B → B → Prop) (esse : Respect)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w)
    (hWhole : WholeRosterNotTrapped m w)
    (hDep : EveryContingentGroundedAt m w) (hEM : ExcludedMiddle)
    (hBridge : NecessityCausesAreActualConcreteGrounds m w CausesNecessityOf)
    (hPrior : SimplyPriorIsActualConcreteGround m w PriorSimply)
    (hGenus : MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn)
    (hHasBeing : NecessaryBeingHasBeing (modalPossible m w) (modalIsAt m) InAct esse)
    (hCause : CauseOfNecessaryBeingCausesItsNecessity (modalPossible m w) (modalIsAt m)
      CausesIn esse CausesNecessityOf) :
    MaximumInBeingIsFirstBeing InAct MoreIn esse PriorSimply := by
  sorry

end TruthCore.Results.Causality.WholeRosterFoundation
