import TruthCore.Greek.Aristotle.Physics.BookVII.Chapter4

namespace TruthCore.Results.Aristotle.Physics.SameAffectionEqualSubjectAlterations
open TruthCore.Greek.Aristotle.Physics

theorem sameAffectionEqualSubjectAlterations
    (SameAffection DifferentAffection EqualAffectedAmount UnequalAffectedAmount
      SameAlteration DifferentAlteration EqualAlteration UnequalAlteration : Prop)
    (hCriterion : AlterationIdentityAndEqualityTrackAffectionAndSubjectReading
      SameAffection DifferentAffection EqualAffectedAmount UnequalAffectedAmount
      SameAlteration DifferentAlteration EqualAlteration UnequalAlteration) :
    SameAffectionEqualSubjectAlterationsReading
      SameAffection EqualAffectedAmount SameAlteration EqualAlteration := by
  sorry

end TruthCore.Results.Aristotle.Physics.SameAffectionEqualSubjectAlterations
