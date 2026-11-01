import TruthCore.Causality.ActualCommonRoot
import TruthCore.Causality.ActualRootUniqueness
import TruthCore.Causality.DirectEsseRootUniquenessAtBeing

namespace TruthCore.Results.Causality.ActualCommonRoot
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessaryConcreteRouteBridge (EsseCauseIsActualConcreteGround)
open TruthCore.Causality.ExistenceActuality (ExistingInActAt)
open TruthCore.Causality.WholeRosterFoundation (WholeRosterNotTrapped)
open TruthCore.Causality.DirectEsseRootUniquenessAtBeing (GradesToMaximumAtBeing)
open TruthCore.Causality.ActualRootUniqueness (UniqueActualRootAt)
open TruthCore.Causality.ActualCommonRoot
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)

/-- Same seven premises give DIRECT common actual-ground coverage, without
contingent dependence or a modal-necessity conclusion. -/
theorem commonRoot {W B R : Type} (m : Profile W B) (w : W)
    (InAct : B → R → Prop) (MoreIn : R → B → B → Prop)
    (CausesIn : B → B → R → Prop) (esse : R)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w)
    (hWhole : WholeRosterNotTrapped m w) (hEM : ExcludedMiddle)
    (hGenus : MaximumInBeingCausesAllBeingsReading InAct MoreIn CausesIn esse)
    (hExisting : ExistingInActAt m.ontic InAct esse w)
    (hEsse : EsseCauseIsActualConcreteGround m w CausesIn esse)
    (hApproach : GradesToMaximumAtBeing InAct MoreIn esse) : ActualCommonRootAt m w := by
  sorry

/-- Common coverage excludes a second actual root constructively, since an
incoming ground contradicts its roothood. No extra EM or C input is used. -/
theorem uniqueRoot {W B : Type} (m : Profile W B) (w : W)
    (hCommon : ActualCommonRootAt m w) : UniqueActualRootAt m w := by
  sorry

end TruthCore.Results.Causality.ActualCommonRoot
