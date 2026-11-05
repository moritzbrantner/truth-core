import TruthCore.Modal.RetainedDuty
namespace TruthCore.Results.Modal.RetainedDuty
open TruthCore.Modal.RetainedDuty
-- Frozen before solution work: exact advertised premises and closed controls.
theorem directCore (s : Case) (hd : PresentDuty s) (hn : PresentInability s)
    (ho : PresentOIC s) : TruthCore.Logic.ConfigurationFalse := by
  sorry
theorem retainedCore (s : Case) (hi : InitialDuty s) (hr : Retention s)
    (hn : PresentInability s) (ho : PresentOIC s) : TruthCore.Logic.ConfigurationFalse := by
  sorry
theorem retentionTransfer (s : Case) (hi : InitialDuty s) (hr : Retention s) :
    PresentDuty s := by
  sorry
theorem controls : Controls := by
  sorry
theorem branching : BranchControls := by
  sorry
end TruthCore.Results.Modal.RetainedDuty
