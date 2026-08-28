import TruthCore.Greek.Aristotle.Physics.BookVI.Chapter4

namespace TruthCore.Results.Aristotle.Physics.EveryChangingSubjectDivisible
open TruthCore.Greek.Aristotle.Physics
/-- Aristotle's divisibility argument in *Physics* VI.4, 234b10-20. -/
theorem everyChangingSubjectDivisible
    (PartAtSource PartAtFirstTerminus ChangingSubjectDivisible : Prop)
    (hParts : ChangingSubjectPartlySourcePartlyTerminusReading PartAtSource PartAtFirstTerminus)
    (hTransition : PartlySourceTerminusImpliesChangingSubjectDivisibleReading
      PartAtSource PartAtFirstTerminus ChangingSubjectDivisible) :
    EveryChangingSubjectDivisibleReading ChangingSubjectDivisible := by
  sorry
end TruthCore.Results.Aristotle.Physics.EveryChangingSubjectDivisible
