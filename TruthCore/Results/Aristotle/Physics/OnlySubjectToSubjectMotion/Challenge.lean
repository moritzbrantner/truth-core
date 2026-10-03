import TruthCore.Greek.Aristotle.Physics.BookV.Chapter1

namespace TruthCore.Results.Aristotle.Physics.OnlySubjectToSubjectMotion

open TruthCore.Greek.Aristotle.Physics

/-- Aristotle's restriction of motion in *Physics* V.1, 225a34-225b3. -/
theorem onlySubjectToSubjectChangeIsMotion
    (SubjectToSubject SubjectToNonSubject NonSubjectToSubject : Prop)
    (hKinds : ThreeKindsOfChangeReading SubjectToSubject SubjectToNonSubject NonSubjectToSubject)
    (hNotMotions :
      GenerationAndCorruptionAreNotMotionsReading SubjectToNonSubject NonSubjectToSubject) :
    OnlySubjectToSubjectChangeIsMotionReading SubjectToSubject := by
  sorry

end TruthCore.Results.Aristotle.Physics.OnlySubjectToSubjectMotion
