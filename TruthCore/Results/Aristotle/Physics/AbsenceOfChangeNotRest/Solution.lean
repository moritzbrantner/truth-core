import TruthCore.Greek.Aristotle.Physics.BookV.Chapter6

namespace TruthCore.Results.Aristotle.Physics.AbsenceOfChangeNotRest

open TruthCore.Greek.Aristotle.Physics

/-- Aristotle's reductio in *Physics* V.6, 230a8-18. -/
theorem absenceOfChangeNotRest
    (AbsenceOfChangeIsRest GenerationIsMotion CorruptionIsMotion : Prop)
    (hConditional :
      AbsenceAsRestWouldMakeGenerationCorruptionMotionsReading
        AbsenceOfChangeIsRest GenerationIsMotion CorruptionIsMotion)
    (hNotMotions :
      GenerationAndCorruptionAreNotMotionsReading CorruptionIsMotion GenerationIsMotion) :
    AbsenceOfChangeIsNotRestReading AbsenceOfChangeIsRest := by
  intro hRest
  exact hNotMotions.2 (hConditional hRest).1

end TruthCore.Results.Aristotle.Physics.AbsenceOfChangeNotRest
