import TruthCore.Causality.NecessaryConcreteRouteBridge

namespace TruthCore.Results.Causality.NecessaryConcreteRouteBridge

open TruthCore.Causality.BruteFoundationBoundary (Profile EveryContingentGroundedAt)
open TruthCore.Causality.NecessaryRootFork (ActualGroundingWF)
open TruthCore.Causality.NecessaryConcreteRouteBridge
open TruthCore.Latin.Aquinas.SummaTheologiae (MaximumInGenusCausesAllInGenusReading)
open TruthCore.Case.Catholicism (MaximumInBeingIsFirstBeing NecessaryBeingHasBeing
  CauseOfNecessaryBeingCausesItsNecessity)
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)

/-- One necessary actual root is necessary per se in the modal reading, and every
maximum in being, if any exists, is identical with it. -/
theorem necessaryRootIsMaximum {W B Respect : Type} (m : Profile W B) (w : W)
    (CausesNecessityOf : B → B → Prop) (InAct : B → Respect → Prop)
    (MoreIn : Respect → B → B → Prop) (CausesIn : B → B → Respect → Prop) (esse : Respect)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w) (hWF : ActualGroundingWF m w)
    (hDep : EveryContingentGroundedAt m w) (hEM : ExcludedMiddle)
    (hBridge : NecessityCausesAreActualConcreteGrounds m w CausesNecessityOf)
    (hGenus : MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn)
    (hHasBeing : NecessaryBeingHasBeing (modalPossible m w) (modalIsAt m) InAct esse)
    (hCause : CauseOfNecessaryBeingCausesItsNecessity (modalPossible m w) (modalIsAt m)
      CausesIn esse CausesNecessityOf) :
    NecessaryRootIsMaximumAt m w CausesNecessityOf InAct MoreIn esse :=
  TruthCore.Causality.NecessaryConcreteRouteBridge.necessaryRootIsMaximum m w CausesNecessityOf
    InAct MoreIn CausesIn esse hPop hWF hDep hEM hBridge hGenus hHasBeing hCause

/-- The route premise that whatever is maximal in being is first, from the necessary
root's premises and four named bridges. No inhabitedness hypothesis. -/
theorem maximumFirstOfNecessaryRoot {W B Respect : Type} (m : Profile W B) (w : W)
    (CausesNecessityOf : B → B → Prop) (InAct : B → Respect → Prop)
    (MoreIn : Respect → B → B → Prop) (CausesIn : B → B → Respect → Prop)
    (PriorSimply : B → B → Prop) (esse : Respect)
    (hWF : ActualGroundingWF m w)
    (hDep : EveryContingentGroundedAt m w) (hEM : ExcludedMiddle)
    (hBridge : NecessityCausesAreActualConcreteGrounds m w CausesNecessityOf)
    (hPrior : SimplyPriorIsActualConcreteGround m w PriorSimply)
    (hGenus : MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn)
    (hHasBeing : NecessaryBeingHasBeing (modalPossible m w) (modalIsAt m) InAct esse)
    (hCause : CauseOfNecessaryBeingCausesItsNecessity (modalPossible m w) (modalIsAt m)
      CausesIn esse CausesNecessityOf) :
    MaximumInBeingIsFirstBeing InAct MoreIn esse PriorSimply :=
  TruthCore.Causality.NecessaryConcreteRouteBridge.maximumFirstOfNecessaryRoot m w CausesNecessityOf
    InAct MoreIn CausesIn PriorSimply esse hWF hDep hEM hBridge hPrior hGenus hHasBeing hCause

/-- The control bundle of `NecessaryRouteControls`. -/
theorem necessaryRouteControls : NecessaryRouteControls :=
  TruthCore.Causality.NecessaryConcreteRouteBridge.necessaryRouteControls

end TruthCore.Results.Causality.NecessaryConcreteRouteBridge
