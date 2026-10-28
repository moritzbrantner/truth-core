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
    simp [popularWin, districtWin, popularCount, localCount, count, h]
  · intro p h
    simp [popularWin, districtWin, popularCount, localCount, count, h]

end TruthCore.Results.Politics.DistrictMajority
