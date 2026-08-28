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
  intro hInfiniteMotion
  rcases hCases hInfiniteMotion with hFiniteInfiniteCase |
      hInfiniteFiniteCase | hInfiniteInfiniteCase
  · exact hFiniteInfinite hFiniteInfiniteCase
  · exact hInfiniteFinite hInfiniteFiniteCase
  · exact hInfiniteInfinite hInfiniteInfiniteCase
end TruthCore.Results.Aristotle.Physics.NoInfiniteMotionInFiniteTime
