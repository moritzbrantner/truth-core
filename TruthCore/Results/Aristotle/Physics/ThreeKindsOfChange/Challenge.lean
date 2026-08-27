import TruthCore.Greek.Aristotle.Physics.BookV.Chapter1

namespace TruthCore.Results.Aristotle.Physics.ThreeKindsOfChange

open TruthCore.Greek.Aristotle.Physics

/-- Aristotle's three-kind classification in *Physics* V.1, 225a3-12. -/
theorem threeKindsOfChange
    (SubjectToSubject SubjectToNonSubject NonSubjectToSubject
      NonSubjectToNonSubject : Prop)
    (hFour :
      FourCandidateChangeCombinationsReading
        SubjectToSubject SubjectToNonSubject NonSubjectToSubject NonSubjectToNonSubject)
    (hExcluded : NonSubjectToNonSubjectIsNotChangeReading NonSubjectToNonSubject) :
    ThreeKindsOfChangeReading SubjectToSubject SubjectToNonSubject NonSubjectToSubject := by
  sorry

end TruthCore.Results.Aristotle.Physics.ThreeKindsOfChange
