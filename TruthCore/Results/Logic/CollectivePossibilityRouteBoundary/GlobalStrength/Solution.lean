module

public import TruthCore.Logic.CollectivePossibilityRouteBoundary

@[expose] public section
namespace TruthCore.Results.Logic.CollectivePossibilityRouteBoundary.GlobalStrength
open TruthCore.Logic
open TruthCore.Logic.CollectivePossibilityRouteBoundary
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- Frozen scope obligation; no historical interpretation or premise truth asserted. -/
theorem globalStrength (f : Frame) (h : EachSometimeNotEntailsSometimeNothing) : LocalShift f := by
  exact h f.Being f.Time f.IsAt

end TruthCore.Results.Logic.CollectivePossibilityRouteBoundary.GlobalStrength
