import TruthCore.Greek.Aristotle.Physics.BookVI.Chapter3

namespace TruthCore.Results.Aristotle.Physics.PrimaryNowIndivisible

open TruthCore.Greek.Aristotle.Physics

/-- Aristotle's conclusion in *Physics* VI.3, 234a20-24. -/
theorem primaryNowIndivisible
    (PastFutureShareSameNow PrimaryNowIndivisible : Prop)
    (hSame : PastFutureShareSameNowReading PastFutureShareSameNow)
    (hTransition :
      SamePrimaryNowImpliesIndivisibleReading
        PastFutureShareSameNow PrimaryNowIndivisible) :
    PrimaryNowIndivisibleReading PrimaryNowIndivisible := by
  sorry

end TruthCore.Results.Aristotle.Physics.PrimaryNowIndivisible
