import TruthCore.Greek.Aristotle.Physics.BookVI.Chapter3

namespace TruthCore.Results.Aristotle.Physics.NothingRestsInNow
open TruthCore.Greek.Aristotle.Physics
/-- Aristotle's rest argument in *Physics* VI.3, 234a31-34. -/
theorem nothingRestsInNow (RestInNow MotionPossibleInNow : Prop)
    (hRequires : RestRequiresMotionCapacityReading RestInNow MotionPossibleInNow)
    (hImpossible : NothingCapableOfMotionInNowReading MotionPossibleInNow) :
    NothingRestsInNowReading RestInNow := by
  intro hRest
  exact hImpossible (hRequires hRest)
end TruthCore.Results.Aristotle.Physics.NothingRestsInNow
