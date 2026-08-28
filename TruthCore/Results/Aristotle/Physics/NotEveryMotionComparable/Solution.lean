import TruthCore.Greek.Aristotle.Physics.BookVII.Chapter4

namespace TruthCore.Results.Aristotle.Physics.NotEveryMotionComparable
open TruthCore.Greek.Aristotle.Physics

theorem notEveryMotionComparable
    (EveryMotionComparable AlterationEqualToLocomotion
      AffectionEqualToLength : Prop)
    (hUniversal : UniversalComparabilityEntailsAlterationLocomotionEqualityReading
      EveryMotionComparable AlterationEqualToLocomotion)
    (hCrossKind :
      AlterationLocomotionEqualityEntailsAffectionLengthEqualityReading
        AlterationEqualToLocomotion AffectionEqualToLength)
    (hImpossible : NoAffectionEqualToLengthReading AffectionEqualToLength) :
    NotEveryMotionComparableReading EveryMotionComparable := by
  intro hEvery
  exact hImpossible (hCrossKind (hUniversal hEvery))

end TruthCore.Results.Aristotle.Physics.NotEveryMotionComparable
