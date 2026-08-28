import TruthCore.Greek.Aristotle.Physics.BookVI.Chapter7
namespace TruthCore.Results.Aristotle.Physics.NoInfiniteMotionInFiniteTime
open TruthCore.Greek.Aristotle.Physics
theorem noInfiniteMotionInFiniteTime
    (InfiniteMotionInFiniteTime FiniteAcrossInfinite InfiniteAcrossFinite
      InfiniteAcrossInfinite : Prop)
    (hCases : InfiniteMotionFiniteTimeConfigurationCasesReading
      InfiniteMotionInFiniteTime FiniteAcrossInfinite InfiniteAcrossFinite
      InfiniteAcrossInfinite)
    (hFiniteInfinite :
      FiniteMovingMagnitudeCannotTraverseInfiniteExtentInFiniteTimeReading
        FiniteAcrossInfinite)
    (hInfiniteFinite :
      InfiniteMovingMagnitudeCannotTraverseFiniteExtentInFiniteTimeReading
        InfiniteAcrossFinite)
    (hInfiniteInfinite :
      InfiniteMovingMagnitudeCannotTraverseInfiniteExtentInFiniteTimeReading
        InfiniteAcrossInfinite) :
    NoInfiniteMotionInFiniteTimeReading InfiniteMotionInFiniteTime := by
  sorry
end TruthCore.Results.Aristotle.Physics.NoInfiniteMotionInFiniteTime
