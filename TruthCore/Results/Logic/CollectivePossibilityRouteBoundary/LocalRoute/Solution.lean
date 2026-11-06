module

public import TruthCore.Logic.CollectivePossibilityRouteBoundary

@[expose] public section
namespace TruthCore.Results.Logic.CollectivePossibilityRouteBoundary.LocalRoute
open TruthCore.Logic
open TruthCore.Logic.CollectivePossibilityRouteBoundary
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- Frozen scope obligation; no historical interpretation or premise truth asserted. -/
theorem localRoute (f : Frame) (hShift : LocalShift f)
    (hDistributive : WhatCanNotBeSometimeIsNotReading f.Possible f.IsAt)
    (hPossible : EmptyRealizedIsPossible f) :
    AllCanNotBeThenNothingPossibleReading f.Possible f.IsAt := by
  intro hAll
  exact hPossible (hShift (fun x => hDistributive x (hAll x)))

end TruthCore.Results.Logic.CollectivePossibilityRouteBoundary.LocalRoute
