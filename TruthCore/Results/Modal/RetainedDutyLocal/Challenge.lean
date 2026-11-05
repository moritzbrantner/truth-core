import TruthCore.Modal.RetainedDutyLocal
namespace TruthCore.Results.Modal.RetainedDutyLocal
open TruthCore.Modal.RetainedDuty
-- New weaker companions frozen separately; old Challenge is unchanged.
theorem universalToLocal (s : Case) (ho : PresentOIC s) : LocalOIC s := by
  sorry
theorem directCore (s : Case) (hd : PresentDuty s) (hn : PresentInability s)
    (ho : LocalOIC s) : TruthCore.Logic.ConfigurationFalse := by
  sorry
theorem retainedCore (s : Case) (hi : InitialDuty s) (hr : Retention s)
    (hn : PresentInability s) (ho : LocalOIC s) : TruthCore.Logic.ConfigurationFalse := by
  sorry
theorem controls : LocalControls := by
  sorry
end TruthCore.Results.Modal.RetainedDutyLocal
