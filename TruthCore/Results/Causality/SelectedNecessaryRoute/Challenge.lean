import TruthCore.Causality.NecessaryConcreteRouteBridge
import TruthCore.Results.Causality.SelectedAncestry.Solution

namespace TruthCore.Results.Causality.SelectedNecessaryRoute

open TruthCore.Causality.BruteFoundationBoundary (Profile EveryContingentGroundedAt)
open TruthCore.Causality.NecessaryRootFork (ActualGroundingWF)
open TruthCore.Causality.NecessaryConcreteRouteBridge
open TruthCore.Latin.Aquinas.SummaTheologiae (MaximumInGenusCausesAllInGenusReading)
open TruthCore.Case.Catholicism (MaximumInBeingIsFirstBeing NecessaryBeingHasBeing
  CauseOfNecessaryBeingCausesItsNecessity)
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)


open TruthCore.Causality.SelectedAncestry
open TruthCore.Causality.NecessaryRootFork (ActualConcrete)
/-- One necessary actual root is necessary per se in the modal reading, and every
maximum in being, if any exists, is identical with it. -/
theorem necessaryRootIsMaximum {W B Respect : Type} (m : Profile W B) (w : W) (selected : B)
    (CausesNecessityOf : B → B → Prop) (InAct : B → Respect → Prop)
    (MoreIn : Respect → B → B → Prop) (CausesIn : B → B → Respect → Prop) (esse : Respect)
    (hActual : ActualConcrete m w selected) (hWF : ConeWellFounded m w selected)
    (hDep : ConeContingentGrounded m w selected) (hEM : ExcludedMiddle)
    (hBridge : NecessityCausesAreActualConcreteGrounds m w CausesNecessityOf)
    (hGenus : MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn)
    (hHasBeing : NecessaryBeingHasBeing (modalPossible m w) (modalIsAt m) InAct esse)
    (hCause : CauseOfNecessaryBeingCausesItsNecessity (modalPossible m w) (modalIsAt m)
      CausesIn esse CausesNecessityOf) :
    NecessaryRootIsMaximumAt m w CausesNecessityOf InAct MoreIn esse := by
  sorry

/-- The route premise that whatever is maximal in being is first, from one complete selected cone and the retained convergence bridges. The selected candidate is explicitly actual; no maximum existence is asserted. -/
theorem maximumFirstOfNecessaryRoot {W B Respect : Type} (m : Profile W B) (w : W) (selected : B)
    (CausesNecessityOf : B → B → Prop) (InAct : B → Respect → Prop)
    (MoreIn : Respect → B → B → Prop) (CausesIn : B → B → Respect → Prop)
    (PriorSimply : B → B → Prop) (esse : Respect)
    (hActual : ActualConcrete m w selected) (hWF : ConeWellFounded m w selected)
    (hDep : ConeContingentGrounded m w selected) (hEM : ExcludedMiddle)
    (hBridge : NecessityCausesAreActualConcreteGrounds m w CausesNecessityOf)
    (hPrior : SimplyPriorIsActualConcreteGround m w PriorSimply)
    (hGenus : MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn)
    (hHasBeing : NecessaryBeingHasBeing (modalPossible m w) (modalIsAt m) InAct esse)
    (hCause : CauseOfNecessaryBeingCausesItsNecessity (modalPossible m w) (modalIsAt m)
      CausesIn esse CausesNecessityOf) :
    MaximumInBeingIsFirstBeing InAct MoreIn esse PriorSimply := by
  sorry

end TruthCore.Results.Causality.SelectedNecessaryRoute
