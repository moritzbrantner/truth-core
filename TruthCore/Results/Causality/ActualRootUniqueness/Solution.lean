import TruthCore.Causality.ActualRootUniqueness
import TruthCore.Causality.DirectEsseRootUniquenessAtBeing
import TruthCore.Results.Causality.WholeRosterFoundation.Solution

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
  obtain ⟨n, hn⟩ :=
    TruthCore.Results.Causality.WholeRosterFoundation.actualRootExists m w hPop hWhole hEM
  -- Restrict only the respect carrier to Unit; B, m, w and esse data are unchanged.
  let act : B → Unit → Prop := fun x _ => InAct x esse
  let more : Unit → B → B → Prop := fun _ y x => MoreIn esse y x
  let cause : B → B → Unit → Prop := fun c x _ => CausesIn c x esse
  obtain ⟨maximum, hMaximum⟩ :=
    TruthCore.Causality.DirectEsseRootRoute.maximumExistsOfExistingRoot
      m w act more () n hn hExisting (fun _ => hApproach) hEM
  have hMaximumN := TruthCore.Causality.DirectEsseRootRoute.maximumEqualsRoot
    m w act more cause () n hn hEM (fun _ => hGenus) hExisting hEsse maximum hMaximum
  refine ⟨n, hn, ?_⟩
  intro x hx
  have hMaximumX := TruthCore.Causality.DirectEsseRootRoute.maximumEqualsRoot
    m w act more cause () x hx hEM (fun _ => hGenus) hExisting hEsse maximum hMaximum
  exact hMaximumX.symm.trans hMaximumN

end TruthCore.Results.Causality.ActualRootUniqueness
