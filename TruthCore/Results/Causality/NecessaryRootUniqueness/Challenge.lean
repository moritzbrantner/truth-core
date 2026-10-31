import TruthCore.Causality.NecessaryRootUniqueness
import TruthCore.Causality.WholeRosterFoundation

namespace TruthCore.Results.Causality.NecessaryRootUniqueness
open TruthCore.Causality.BruteFoundationBoundary
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
  sorry

end TruthCore.Results.Causality.NecessaryRootUniqueness
