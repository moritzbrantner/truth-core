import TruthCore.Greek.Aristotle.Physics.BookIV.Chapter13

namespace TruthCore.Results.Aristotle.Physics.TimeMotionSameRecurrence

open TruthCore.Greek.Aristotle.Physics

/-- Aristotle's *Physics* IV.13 recurrence argument, 222a28-222b1. -/
theorem motionTimeRecurrenceCovaries
    (SameTimeRecurs SameMotionRecurs : Prop)
    (hSameMotion :
      SameRecurringMotionEntailsSameRecurringTimeReading SameMotionRecurs SameTimeRecurs)
    (hDifferentMotion :
      DifferentRecurringMotionEntailsDifferentRecurringTimeReading SameMotionRecurs SameTimeRecurs) :
    MotionTimeRecurrenceCovariesReading SameMotionRecurs SameTimeRecurs := by
  sorry

end TruthCore.Results.Aristotle.Physics.TimeMotionSameRecurrence
