module
public import TruthCore.Modal.RetainedDutyLocal
public import TruthCore.Results.Modal.RetainedDuty.Solution
@[expose] public section
namespace TruthCore.Results.Modal.RetainedDutyLocal
open TruthCore.Modal.RetainedDuty

theorem universalToLocal (s : Case) (ho : PresentOIC s) : LocalOIC s := by
  intro hd
  exact ho .originalReturn hd

theorem directCore (s : Case) (hd : PresentDuty s) (hn : PresentInability s)
    (ho : LocalOIC s) : TruthCore.Logic.ConfigurationFalse := by
  have canReturn := ho hd
  exact hn canReturn

theorem retainedCore (s : Case) (hi : InitialDuty s) (hr : Retention s)
    (hn : PresentInability s) (ho : LocalOIC s) : TruthCore.Logic.ConfigurationFalse := by
  have hd := TruthCore.Results.Modal.RetainedDuty.retentionTransfer s hi hr
  exact directCore s hd hn ho

theorem controls : LocalControls := by
  let old := TruthCore.Results.Modal.RetainedDuty.controls
  rcases old with ⟨n, a, c, never, l, ar, cr, _⟩
  have hc : ¬ LocalOIC crash := fun h => Stage.noConfusion (h rfl)
  refine ⟨⟨n.1, universalToLocal _ n.2.1, n.2.2⟩,
    ⟨a.1, universalToLocal _ a.2.1, a.2.2⟩, ⟨c.1, c.2.1, hc⟩,
    ⟨never.1, never.2.1, universalToLocal _ never.2.2.1, never.2.2.2⟩,
    ⟨l.1, l.2.1, universalToLocal _ l.2.2.1, l.2.2.2.1⟩,
    ⟨ar.1, ar.2.1, universalToLocal _ ar.2.2⟩, cr, ?_, ?_⟩
  · exact ⟨fun _ => rfl,
      fun h => Action.noConfusion (h .compensation (Or.inr rfl)),
      Or.inl rfl, rfl, Or.inr rfl, Action.noConfusion⟩
  · exact ⟨fun _ => rfl,
      fun h => Action.noConfusion (h .debtRepayment (Or.inr rfl)),
      Or.inl rfl, rfl, Or.inr rfl, Action.noConfusion⟩

namespace Evaluations
open TruthCore.Results.Modal.RetainedDuty.Evaluations
theorem noDutyLocal : LocalOIC noDuty := universalToLocal _ noDuty2
theorem ableReturnLocal : LocalOIC ableReturn := universalToLocal _ ableReturn2
theorem crashLocal : ¬ LocalOIC crash := fun h => Stage.noConfusion (h rfl)
theorem lapseLocal : LocalOIC lapse := universalToLocal _ lapse2
theorem neverOwedLocal : LocalOIC neverOwed := universalToLocal _ neverOwed2
end Evaluations
end TruthCore.Results.Modal.RetainedDutyLocal
