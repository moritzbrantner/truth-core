import TruthCore.Causality.ActualRootUniqueness
import TruthCore.Causality.DirectEsseRootUniquenessAtBeing

namespace TruthCore.Results.Causality.ActualRootUniqueness
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessaryConcreteRouteBridge (EsseCauseIsActualConcreteGround)
open TruthCore.Causality.ExistenceActuality (ExistingInActAt)
open TruthCore.Causality.WholeRosterFoundation (WholeRosterNotTrapped)
open TruthCore.Causality.DirectEsseRootUniquenessAtBeing (GradesToMaximumAtBeing)
open TruthCore.Causality.ActualRootUniqueness
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)

/-- Fixed-esse maximum comparison identifies every actual selected root.
No contingent-dependence or modal-necessity claim is included. -/
theorem uniqueRoot {W B R : Type} (m : Profile W B) (w : W)
    (InAct : B → R → Prop) (MoreIn : R → B → B → Prop)
    (CausesIn : B → B → R → Prop) (esse : R)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w)
    (hWhole : WholeRosterNotTrapped m w) (hEM : ExcludedMiddle)
    (hGenus : MaximumInBeingCausesAllBeingsReading InAct MoreIn CausesIn esse)
    (hExisting : ExistingInActAt m.ontic InAct esse w)
    (hEsse : EsseCauseIsActualConcreteGround m w CausesIn esse)
    (hApproach : GradesToMaximumAtBeing InAct MoreIn esse) : UniqueActualRootAt m w := by
  sorry

end TruthCore.Results.Causality.ActualRootUniqueness
