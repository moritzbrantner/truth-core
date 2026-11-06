import TruthCore.Logic.CollectivePossibilityRouteBoundary

namespace TruthCore.Results.Logic.CollectivePossibilityRouteBoundary.Countercase
open TruthCore.Logic
open TruthCore.Logic.CollectivePossibilityRouteBoundary
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- Frozen scope obligation; no historical interpretation or premise truth asserted. -/
theorem countercase (f : Frame) (hAll : AllIndividuallyPossible f)
    (hNotJoint : JointAbsenceImpossible f) : CollectiveFails f := by
  sorry

end TruthCore.Results.Logic.CollectivePossibilityRouteBoundary.Countercase
