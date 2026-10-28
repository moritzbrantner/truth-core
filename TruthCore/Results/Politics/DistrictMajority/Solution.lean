import TruthCore.Politics.DistrictMajority

namespace TruthCore.Results.Politics.DistrictMajority
open TruthCore.Politics.DistrictMajority

/-- Equal-sized districts and equal ballots admit a majority reversal.
Regrouping the same five A / four B ballots restores agreement; unanimity
for either party cannot reverse. No normative conclusion is encoded. -/
theorem certificate : Certificate := by
  refine ⟨by decide, by unfold popularWin; decide, by unfold districtWin; decide,
    by decide, by unfold districtWin; decide, ?_, ?_⟩
  · intro p h
    have hp : p = (fun _ _ => true) := by
      funext d v
      exact h d v
    rw [hp]
    exact ⟨by unfold popularWin; decide, by unfold districtWin; decide⟩
  · intro p h
    have hp : p = (fun _ _ => false) := by
      funext d v
      exact h d v
    rw [hp]
    exact ⟨by unfold popularWin; decide, by unfold districtWin; decide⟩

end TruthCore.Results.Politics.DistrictMajority
