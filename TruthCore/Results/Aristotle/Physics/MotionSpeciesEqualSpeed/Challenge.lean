import TruthCore.Greek.Aristotle.Physics.BookVII.Chapter4

namespace TruthCore.Results.Aristotle.Physics.MotionSpeciesEqualSpeed
open TruthCore.Greek.Aristotle.Physics

theorem motionSpeciesEqualSpeed
    (MotionHasSpecies MotionsEqualSpeed MotionsDifferInSpecies : Prop)
    (hSpecies : MotionHasSpeciesReading MotionHasSpecies)
    (hCriterion : MotionSpeciesAccountEntailsEqualSpeedSpeciesIdentityReading
      MotionHasSpecies MotionsEqualSpeed MotionsDifferInSpecies) :
    SpeciesDifferentMotionsNotEqualSpeedReading
      MotionsDifferInSpecies MotionsEqualSpeed := by
  sorry

end TruthCore.Results.Aristotle.Physics.MotionSpeciesEqualSpeed
