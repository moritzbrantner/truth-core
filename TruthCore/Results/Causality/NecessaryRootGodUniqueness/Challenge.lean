import TruthCore.Causality.WholeRosterFoundation
import TruthCore.Causality.NecessaryConcreteRouteBridge
import TruthCore.Case.Catholicism.StageTwo

namespace TruthCore.Results.Causality.NecessaryRootGodUniqueness
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.WholeRosterFoundation
open TruthCore.Causality.NecessaryConcreteRouteBridge
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)
open TruthCore.Latin.Aquinas.SummaTheologiae (MaximumInGenusCausesAllInGenusReading)
open TruthCore.Case.Catholicism

/-- Any God is a maximum by the explicit nominal converse; every maximum equals
one supplied necessary root. This proves at most one God, not God existence or
uniqueness of all necessary individuals, and needs no maximum-existence premise. -/
theorem godIsOne {W B Respect : Type} (m : Profile W B) (w : W)
    (CausesNecessityOf : B → B → Prop) (InAct : B → Respect → Prop)
    (MoreIn : Respect → B → B → Prop) (CausesIn : B → B → Respect → Prop)
    (esse : Respect) (IsGod : B → Prop)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w)
    (hWhole : WholeRosterNotTrapped m w)
    (hDep : EveryContingentGroundedAt m w) (hEM : ExcludedMiddle)
    (hBridge : NecessityCausesAreActualConcreteGrounds m w CausesNecessityOf)
    (hGenus : MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn)
    (hHasBeing : NecessaryBeingHasBeing (modalPossible m w) (modalIsAt m) InAct esse)
    (hCause : CauseOfNecessaryBeingCausesItsNecessity (modalPossible m w) (modalIsAt m)
      CausesIn esse CausesNecessityOf)
    (hMaximal : GodIsMaximalInBeing IsGod InAct MoreIn esse) :
    GodIsOne IsGod := by
  sorry

end TruthCore.Results.Causality.NecessaryRootGodUniqueness
