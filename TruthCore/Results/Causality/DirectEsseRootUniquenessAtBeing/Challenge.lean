import TruthCore.Causality.DirectEsseRootUniquenessAtBeing
import TruthCore.Causality.DirectEsseRootRoute
import TruthCore.Causality.NecessaryRootUniqueness
import TruthCore.Causality.WholeRosterFoundation

namespace TruthCore.Results.Causality.DirectEsseRootUniquenessAtBeing
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryConcreteRouteBridge
open TruthCore.Causality.ExistenceActuality (ExistingInActAt)
open TruthCore.Causality.NecessaryRootUniqueness
open TruthCore.Causality.WholeRosterFoundation
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)

open TruthCore.Causality.DirectEsseRootUniquenessAtBeing
theorem uniqueRoot {W B Respect : Type} (m : Profile W B) (w : W)
    (InAct : B → Respect → Prop) (MoreIn : Respect → B → B → Prop)
    (CausesIn : B → B → Respect → Prop) (esse : Respect)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w)
    (hWhole : WholeRosterNotTrapped m w)
    (hDep : EveryContingentGroundedAt m w) (hEM : ExcludedMiddle)
    (hGenus : MaximumInBeingCausesAllBeingsReading InAct MoreIn CausesIn esse)
    (hExisting : ExistingInActAt m.ontic InAct esse w)
    (hEsse : EsseCauseIsActualConcreteGround m w CausesIn esse)
    (hApproach : GradesToMaximumAtBeing InAct MoreIn esse) :
    UniqueNecessaryActualRootAt m w := by
  sorry

end TruthCore.Results.Causality.DirectEsseRootUniquenessAtBeing
