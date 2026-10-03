import TruthCore.Greek.Aristotle.Physics.BookVII.Chapter4

namespace TruthCore.Results.Aristotle.Physics.SharedMeaningNotSufficient
open TruthCore.Greek.Aristotle.Physics

theorem sharedMeaningNotSufficient
    (SharedMeaningSufficientForComparability WaterAndAirAmountsComparable : Prop)
    (hWouldCompare : SharedMeaningSufficiencyWouldCompareWaterAndAirReading
      SharedMeaningSufficientForComparability WaterAndAirAmountsComparable)
    (hIncomparable : WaterAndAirAmountsNotComparableReading
      WaterAndAirAmountsComparable) :
    SharedMeaningNotSufficientForComparabilityReading
      SharedMeaningSufficientForComparability := by
  sorry

end TruthCore.Results.Aristotle.Physics.SharedMeaningNotSufficient
